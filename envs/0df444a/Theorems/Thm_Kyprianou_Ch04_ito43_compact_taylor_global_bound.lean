-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_compact_taylor_global_bound
-- name    : Kyprianou.Ch04.ito43_compact_taylor_global_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:27:08.689532+00:00
-- url     : https://prove2.me/theorems/e3ebfd3b-74bc-4d28-995f-10cdc83ae92e
-- title:
--   Uniform quadratic Taylor and second derivative bounds on compact rectangles
-- statement:
--   Uniform quadratic Taylor and second derivative bounds on compact rectangles.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Set
set_option autoImplicit false

/-- A compact time-space rectangle bounds both the second derivative and the uncentred Taylor remainder. -/

theorem Kyprianou.Ch04.ito43_compact_taylor_global_bound (f : ℝ × ℝ → ℝ) (T M : ℝ)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x : ℝ => f (s,x)))
    (hg : ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Icc 0 T ×ˢ Icc (-M) M)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s ∈ Icc 0 T, ∀ x ∈ Icc (-M) M,
        |iteratedDeriv 2 (fun z : ℝ => f (s,z)) x| ≤ C) ∧
      (∀ s ∈ Icc 0 T, ∀ x ∈ Icc (-M) M, ∀ y ∈ Icc (-M) M,
        |f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x)| ≤ C*(y-x)^2/2) := by sorry
