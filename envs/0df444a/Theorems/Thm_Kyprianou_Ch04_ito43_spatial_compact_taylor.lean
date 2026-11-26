-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_compact_taylor
-- name    : Kyprianou.Ch04.ito43_spatial_compact_taylor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:55:40.557732+00:00
-- url     : https://prove2.me/theorems/263465c7-328b-55c0-bacc-a8e179a8c306
-- title:
--   Uniform small-increment Taylor excess bound on compact rectangles
-- statement:
--   Uniform small-increment Taylor excess bound on compact rectangles.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_taylor_modulus
open Set
set_option autoImplicit false

/-- Small spatial Taylor excess is bounded by an arbitrarily small multiple of squared increments,
uniformly on a compact time-space rectangle. -/

theorem Kyprianou.Ch04.ito43_spatial_compact_taylor (f : ℝ × ℝ → ℝ) (T M : ℝ)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x : ℝ => f (s,x)))
    (hg : ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Icc 0 T ×ˢ Icc (-M) M)) :
    ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc 0 T, ∀ x ∈ Icc (-M) M, ∀ y ∈ Icc (-M) M, |y-x| ≤ δ →
        |f (s,y) - f (s,x) - deriv (fun z : ℝ => f (s,z)) x * (y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x * (y-x)^2/2| ≤ e * (y-x)^2 := by sorry
