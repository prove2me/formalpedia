-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_measure_scaling
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:55:15.448903+00:00
-- url     : https://prove2.me/theorems/8871dbac-8454-4911-bd84-4f72d6b8f3c0
-- title:
--   ENNReal measure scaling for the nonnegative simplex cutoff
-- statement:
--   The ENNReal volume of the nonnegative simplex with coordinate sum at most r equals the unit simplex volume multiplied by the ENNReal encoding of r^n, for every r ≥ 0.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling
    (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ r} =
      ENNReal.ofReal (r ^ n) *
        MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
          ∑ i : Fin n, y i ≤ 1} := by
  sorry
