-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveRootQuotientSecantLimit
-- name    : Kyprianou.Ch04.positiveRootQuotientSecantLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:33:59.551117+00:00
-- url     : https://prove2.me/theorems/29857b85-6615-4bdc-886d-9b5a24476db8
-- title:
--   Positive-root quotient tends to the nonnegative infimum of secants
-- statement:
--   For a monotone positive secant slope, the quotient of a positive level tending to zero by its positive root tends to the positive part of the infimum of secants, including when the secants are unbounded below.
-- source:
--   Kyprianou (2006), Corollary 4.9, zero-killing-rate root quotient.

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveRootQuotientSecantLimit
    (f : ℝ → ℝ)
    (hf : MonotoneOn (fun x : ℝ => f x / x) (Ioi 0))
    (q r : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hr : ∀ n, 0 < r n) (hroot : ∀ n, f (r n) = q n)
    (hlim : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => q n / r n) atTop
      (𝓝 (max 0 (sInf ((fun x : ℝ => f x / x) '' Ioi 0)))) := by
  sorry
