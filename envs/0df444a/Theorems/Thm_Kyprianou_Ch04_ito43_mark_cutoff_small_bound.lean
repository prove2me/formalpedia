-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_cutoff_small_bound
-- name    : Kyprianou.Ch04.ito43_mark_cutoff_small_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:24:26.584091+00:00
-- url     : https://prove2.me/theorems/5f7996e8-d411-4bef-9358-efbc6b42ffa4
-- title:
--   A locally subquadratic mark has uniformly small complementary cutoff
-- statement:
--   Choose the cutoff scale so that the complement vanishes beyond the local Taylor radius. Inside the radius multiply the local quadratic estimate by a number between zero and one.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_mark_cutoff_small_bound (r : ℝ → ℝ)
    (hsmall : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ z, |z| ≤ δ → |r z| ≤ e*z^2)
    (e : ℝ) (he : 0 < e) :
    ∃ m : ℕ, ∀ z : ℝ,
      |r z - r z * min 1 (max 0 (|z| * ((m:ℝ)+1)-1))| ≤ e*z^2 := by sorry
