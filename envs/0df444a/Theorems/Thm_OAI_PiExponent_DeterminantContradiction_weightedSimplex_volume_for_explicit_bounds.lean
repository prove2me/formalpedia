-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_for_explicit_bounds
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_for_explicit_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:38:26.450747+00:00
-- url     : https://prove2.me/theorems/3379c5e8-d5ea-42ad-a78e-9b8a5bf0868c
-- title:
--   Volume formula for the simplex in the explicit bounds argument
-- statement:
--   For positive weights and positive cutoff A, the volume of the nonnegative weighted simplex is A^m divided by m! and the product of the weights. The formula also covers m = 0, where both sides are 1. This removes the measure computation from the parent; scaling coordinates by the weights and computing the standard simplex volume gives an independent proof route.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_for_explicit_bounds {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal =
      A ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
