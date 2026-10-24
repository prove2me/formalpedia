-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedUnitBoxes_volume_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.weightedUnitBoxes_volume_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:34:43.45008+00:00
-- url     : https://prove2.me/theorems/8c3c7006-8248-46c1-8d6e-69969cb712af
-- title:
--   The unit boxes have total volume equal to the lattice count
-- statement:
--   The union of the half-open unit boxes based at the finite weighted simplex has real-valued volume equal to the number of lattice points.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedUnitBoxes_volume_toReal {m : Nat} (w : Fin m → Real) (B : Real) :
    (MeasureTheory.volume
      (⋃ a ∈ OAI.PiExponent.realWeightedSimplex w B,
        {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1})).toReal =
      ((OAI.PiExponent.realWeightedSimplex w B).card : Real) := by sorry
