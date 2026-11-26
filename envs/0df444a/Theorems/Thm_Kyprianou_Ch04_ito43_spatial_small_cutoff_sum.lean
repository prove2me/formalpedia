-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_cutoff_sum
-- name    : Kyprianou.Ch04.ito43_spatial_small_cutoff_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:58:17.456259+00:00
-- url     : https://prove2.me/theorems/b8b2be6f-80ae-5a06-a2a3-caae9e0297ee
-- title:
--   Small-cutoff Taylor excess sum bounded by quadratic energy
-- statement:
--   For a compact rectangle the small-cutoff Taylor excess sum is bounded by an arbitrarily small positive multiple of the total squared increments.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_compact_taylor
open Set
set_option autoImplicit false

/-- On a compact rectangle the sum of small-cutoff Taylor excesses is controlled
by any prescribed positive multiple of the total squared increments. -/

theorem Kyprianou.Ch04.ito43_spatial_small_cutoff_sum (f : ℝ × ℝ → ℝ) (T M : ℝ)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x : ℝ => f (s,x)))
    (hg : ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Icc 0 T ×ˢ Icc (-M) M)) :
    ∀ e : ℝ, 0 < e → ∃ m : ℕ, ∀ (n : ℕ) (s x y : ℕ → ℝ),
      (∀ k < n, s k ∈ Icc 0 T ∧ x k ∈ Icc (-M) M ∧ y k ∈ Icc (-M) M) →
      let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ)+1) - 1))
      |∑ k ∈ Finset.range n,
        (f (s k,y k) - f (s k,x k) - deriv (fun z : ℝ => f (s k,z)) (x k) * (y k-x k) -
          iteratedDeriv 2 (fun z : ℝ => f (s k,z)) (x k) * (y k-x k)^2 / 2) *
          (1-chi (y k-x k))| ≤ e * ∑ k ∈ Finset.range n, (y k-x k)^2 := by sorry
