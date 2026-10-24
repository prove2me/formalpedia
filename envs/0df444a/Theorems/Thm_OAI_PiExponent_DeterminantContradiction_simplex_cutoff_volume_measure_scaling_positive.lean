-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_measure_scaling_positive
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_positive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:59:01.074539+00:00
-- url     : https://prove2.me/theorems/caab7f03-aea9-41e9-b950-8e27ac024d4c
-- title:
--   Positive-radius simplex volume scaling
-- statement:
--   For a strictly positive cutoff, the nonnegative simplex is the scalar image of the unit simplex, and its volume scales by r^n. This removes the positive-radius measure-scaling argument from the parent. A proof route is to identify the cutoff set with the image of the unit simplex under scalar multiplication by r, then apply the linear-map volume formula to the scalar linear map on Fin n → Real, whose determinant is r^n. The child retains positivity because the linear map must be invertible.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_positive
    (n : Nat) (r : Real) (hr : 0 ≤ r) (hpos : 0 < r) :
    MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ r} =
      ENNReal.ofReal (r ^ n) *
        MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
          ∑ i : Fin n, y i ≤ 1} := by sorry
