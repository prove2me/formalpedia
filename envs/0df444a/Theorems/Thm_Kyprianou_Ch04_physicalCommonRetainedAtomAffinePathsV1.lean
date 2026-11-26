-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
-- name    : Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:44:15.144453+00:00
-- url     : https://prove2.me/theorems/c8a32d63-549e-4edc-aba6-9866c27656ea
-- title:
--   Common retained atom representations of both physical cutoff paths
-- statement:
--   Represent the two physical paths on a single retained marked atom set. The large and small bands partition that set exactly.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalCommonRetainedAtomAffinePathsV1 (R : Measure (ℝ × ℝ)) (T : NNReal) (e b c : ℝ)
    (he : e < 1) (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r)) :
    ∀ t : NNReal, t ≤ T →
      b * (t : ℝ) + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
        {x : ℝ | 1 ≤ |x|}, z.2 ∂ R) =
      b * (t : ℝ) + (∑ r ∈ S, if r ≤ t then (if 1 ≤ |j r| then j r else 0) else 0) ∧
      b * (t : ℝ) + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
        {x : ℝ | 1 ≤ |x|}, z.2 ∂ R) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
          {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂ R) - (t : ℝ)*c =
      (b-c) * (t : ℝ) + ∑ r ∈ S, if r ≤ t then j r else 0 := by
  sorry
end Kyprianou.Ch04
