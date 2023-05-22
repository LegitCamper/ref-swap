#![cfg_attr(not(test), no_std)]
//! Safe wrapper around [`AtomicPtr`](core::sync::atomic::AtomicPtr).
//! Instead of swapping a pointer, it works with references and lifetimes, allowing a safe API.
//!
//! Two versions are provided:
//! - [`RefSwap`][] for swapping references
//! - [`OptionRefSwap`][] for swapping `Option<&T>`
//!
//! [`OptionRefSwap`][] encodes `None` as a null pointer and has no additionnal overhead.

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicPtr, Ordering},
};

/// A reference that can atomically be changed using another reference with the same lifetime and type
pub struct RefSwap<'a, T> {
    ptr: AtomicPtr<T>,
    phantom: PhantomData<&'a T>,
}

impl<'a, T> RefSwap<'a, T> {
    pub const fn new(data: &'a T) -> Self {
        Self {
            ptr: AtomicPtr::new(data as *const _ as *mut _),
            phantom: PhantomData,
        }
    }

    /// Stores a reference if the current value is the same as the current value.
    ///
    /// Be aware that the comparison is only between the reference, not between the value.
    /// If current point to another adress in memory than the reference currently holds, it will fail,
    /// Even if both are equal according to a `PartialEq` implementation.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::compare_and_swap`](core::sync::atomic::AtomicPtr::compare_and_swap)
    #[deprecated(note = "Use `compare_exchange` or `compare_exchange_weak` instead")]
    pub fn compare_and_swap(&self, current: &'a T, new: &'a T, order: Ordering) -> &'a T {
        #[allow(deprecated)]
        let ptr = self.ptr.compare_and_swap(
            current as *const _ as *mut _,
            new as *const _ as *mut _,
            order,
        );

        // Safety: the pointer can only be set to a reference that lives for &'a
        unsafe { &*ptr }
    }

    /// Stores a reference if the current value is the same as the current value.
    ///
    /// Be aware that the comparison is only between the reference, not between the value.
    /// If current point to another adress in memory than the reference currently holds, it will fail,
    /// Even if both are equal according to a `PartialEq` implementation.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::compare_exchange`](core::sync::atomic::AtomicPtr::compare_exchange)
    pub fn compare_exchange(
        &self,
        current: &'a T,
        new: &'a T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<&'a T, &'a T> {
        let res = self.ptr.compare_exchange(
            current as *const _ as *mut _,
            new as *const _ as *mut _,
            success,
            failure,
        );

        // Safety: the pointer can only be set to a reference that lives for &'a
        res.map(|ptr| unsafe { &*ptr })
            .map_err(|ptr| unsafe { &*ptr })
    }

    /// Stores a reference if the current value is the same as the current value.
    ///
    /// Be aware that the comparison is only between the reference, not between the value.
    /// If current point to another adress in memory than the reference currently holds, it will fail,
    /// Even if both are equal according to a `PartialEq` implementation.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::compare_exchange_weak`](core::sync::atomic::AtomicPtr::compare_exchange_weak)
    pub fn compare_exchange_weak(
        &self,
        current: &'a T,
        new: &'a T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<&'a T, &'a T> {
        let res = self.ptr.compare_exchange_weak(
            current as *const _ as *mut _,
            new as *const _ as *mut _,
            success,
            failure,
        );

        // Safety: the pointer can only be set to a reference that lives for &'a
        res.map(|ptr| unsafe { &*ptr })
            .map_err(|ptr| unsafe { &*ptr })
    }

    /// Get a mutable reference to the current stored reference.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
    pub fn get_mut<'s>(&'s mut self) -> &'s mut &'a T {
        let res: &'s mut *mut T = self.ptr.get_mut();
        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { &mut *(res as *mut *mut T as *mut &'a T) }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are concurrently accessing the atomic data.
    pub fn into_inner(self) -> &'a T {
        let res = self.ptr.into_inner();
        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { &*res }
    }

    /// Fetches the value, and applies a function to it that returns an optional new value. `Returns` a `Result` of `Ok(previous_value)` if the function returned `Some(_)`, else `Err(previous_value)`.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::fetch_update`](core::sync::atomic::AtomicPtr::fetch_update)
    pub fn fetch_update<F: FnMut(&'a T) -> Option<&'a T>>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        mut f: F,
    ) -> Result<&'a T, &'a T> {
        self.ptr
            .fetch_update(set_order, fetch_order, |ptr| {
                f(
                    // Safety: we know that the *mut T is always set to a `&'a T`
                    unsafe { &*ptr },
                )
                .map(|r| r as *const _ as *mut _)
            })
            // Safety: we know that the *mut T is always set to a `&'a T`
            .map(|ptr| unsafe { &*ptr })
            .map_err(|ptr| unsafe { &*ptr })
    }

    /// Loads a value
    pub fn load(&self, order: Ordering) -> &'a T {
        let res = self.ptr.load(order);

        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { &*res }
    }

    /// Store a value
    pub fn store(&self, ptr: &'a T, order: Ordering) {
        self.ptr.store(ptr as *const _ as *mut _, order);
    }

    /// Stores a value into the pointer, returning the previous value.
    pub fn swap(&self, ptr: &'a T, order: Ordering) -> &'a T {
        let res = self.ptr.swap(ptr as *const _ as *mut _, order);

        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { &*res }
    }
}

/// An optionnal reference that can atomically be changed to another optionnal reference with the same lifetime and type
pub struct OptionRefSwap<'a, T> {
    ptr: AtomicPtr<T>,
    phantom: PhantomData<&'a T>,
}

/// Returns a null pointer if `ptr` is None, otherwise returns the the pointer corresponding to the reference
const fn opt_to_ptr<T>(ptr: Option<&T>) -> *mut T {
    match ptr {
        Some(r) => r as *const _ as *mut _,
        None => core::ptr::null_mut(),
    }
}

/// # Safety: `ptr` must come from `opt_to_ptr` with the corresponding lifetime
unsafe fn ptr_to_opt<'a, T>(ptr: *mut T) -> Option<&'a T> {
    if ptr.is_null() {
        None
    } else {
        // Safety: we know that ptr comes from `opt_to_ptr`, and therefor is a `&'a T` when not null
        Some(unsafe { &*ptr })
    }
}

impl<'a, T> OptionRefSwap<'a, T> {
    pub const fn new(data: Option<&'a T>) -> Self {
        Self {
            ptr: AtomicPtr::new(opt_to_ptr(data)),
            phantom: PhantomData,
        }
    }

    /// Stores a reference if the current value is the same as the current value.
    ///
    /// Be aware that the comparison is only between the reference, not between the value.
    /// If current point to another adress in memory than the reference currently holds, it will fail,
    /// Even if both are equal according to a `PartialEq` implementation.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::compare_and_swap`](core::sync::atomic::AtomicPtr::compare_and_swap)
    #[deprecated(note = "Use `compare_exchange` or `compare_exchange_weak` instead")]
    pub fn compare_and_swap(
        &self,
        current: Option<&'a T>,
        new: Option<&'a T>,
        order: Ordering,
    ) -> Option<&'a T> {
        #[allow(deprecated)]
        let ptr = self
            .ptr
            .compare_and_swap(opt_to_ptr(current), opt_to_ptr(new), order);

        // Safety: the pointer can only be set to a reference that lives for &'a
        unsafe { ptr_to_opt(ptr) }
    }

    /// Stores a reference if the current value is the same as the current value.
    ///
    /// Be aware that the comparison is only between the reference, not between the value.
    /// If current point to another adress in memory than the reference currently holds, it will fail,
    /// Even if both are equal according to a `PartialEq` implementation.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::compare_exchange`](core::sync::atomic::AtomicPtr::compare_exchange)
    pub fn compare_exchange(
        &self,
        current: Option<&'a T>,
        new: Option<&'a T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Option<&'a T>, Option<&'a T>> {
        let res = self
            .ptr
            .compare_exchange(opt_to_ptr(current), opt_to_ptr(new), success, failure);

        // Safety: the pointer can only be set to a reference that lives for &'a
        res.map(|ptr| unsafe { ptr_to_opt(ptr) })
            .map_err(|ptr| unsafe { ptr_to_opt(ptr) })
    }

    /// Stores a reference if the current value is the same as the current value.
    ///
    /// Be aware that the comparison is only between the reference, not between the value.
    /// If current point to another adress in memory than the reference currently holds, it will fail,
    /// Even if both are equal according to a `PartialEq` implementation.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::compare_exchange_weak`](core::sync::atomic::AtomicPtr::compare_exchange_weak)
    pub fn compare_exchange_weak(
        &self,
        current: Option<&'a T>,
        new: Option<&'a T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Option<&'a T>, Option<&'a T>> {
        let res =
            self.ptr
                .compare_exchange_weak(opt_to_ptr(current), opt_to_ptr(new), success, failure);

        // Safety: the pointer can only be set to a reference that lives for &'a
        res.map(|ptr| unsafe { ptr_to_opt(ptr) })
            .map_err(|ptr| unsafe { ptr_to_opt(ptr) })
    }

    /// Get a mutable reference to the current stored reference.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
    #[allow(unused)]
    fn get_mut<'s>(&'s mut self) -> &'s mut Option<&'a T> {
        let res: &'s mut *mut T = self.ptr.get_mut();

        // TODO: Is this transmute really safe? Making this function private until I'm sure

        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { core::mem::transmute(res) }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are concurrently accessing the atomic data.
    pub fn into_inner(self) -> &'a T {
        let res = self.ptr.into_inner();
        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { &*res }
    }

    /// Fetches the value, and applies a function to it that returns an optional new value. `Returns` a `Result` of `Ok(previous_value)` if the function returned `Some(_)`, else `Err(previous_value)`.
    ///
    /// For more information on the orderings, se the documentation of [`AtomicPtr::fetch_update`](core::sync::atomic::AtomicPtr::fetch_update)
    pub fn fetch_update<F: FnMut(Option<&'a T>) -> Option<Option<&'a T>>>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        mut f: F,
    ) -> Result<Option<&'a T>, Option<&'a T>> {
        self.ptr
            .fetch_update(set_order, fetch_order, |ptr| {
                f(
                    // Safety: we know that the *mut T is always set to a `Option<&'a T>`
                    unsafe { ptr_to_opt(ptr) },
                )
                .map(opt_to_ptr)
            })
            // Safety: we know that the *mut T is always set to a `&'a T`
            .map(|ptr| unsafe { ptr_to_opt(ptr) })
            .map_err(|ptr| unsafe { ptr_to_opt(ptr) })
    }

    /// Loads a value
    pub fn load(&self, order: Ordering) -> Option<&'a T> {
        let res = self.ptr.load(order);

        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { ptr_to_opt(res) }
    }

    /// Stores a value
    pub fn store(&self, ptr: Option<&'a T>, order: Ordering) {
        self.ptr.store(opt_to_ptr(ptr), order);
    }

    /// Stores a value into the pointer, returning the previous value.
    pub fn swap(&self, ptr: Option<&'a T>, order: Ordering) -> Option<&'a T> {
        let res = self.ptr.swap(opt_to_ptr(ptr), order);

        // Safety: we know that the *mut T is always set to a `&'a T`
        unsafe { ptr_to_opt(res) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(unused)]
    fn variance<'a, 'b>(a: &'a u32, b: Option<&'b u32>) {
        let r = RefSwap::new(a);
        let stat: &'static u32 = &123;
        r.store(stat, Ordering::Relaxed);

        let r = OptionRefSwap::new(b);
        let stat: Option<&'static u32> = Some(&123);
        r.store(b, Ordering::Relaxed);
    }
}
