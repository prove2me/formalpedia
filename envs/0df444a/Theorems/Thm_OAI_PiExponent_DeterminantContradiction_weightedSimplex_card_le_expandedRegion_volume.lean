-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_expandedRegion_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expandedRegion_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:01:24.563207+00:00
-- url     : https://prove2.me/theorems/603976e9-c2a1-4b06-ae1a-102281bc2859
-- title:
--   Unit boxes bound the weighted lattice count
-- statement:
--   The number of strict weighted lattice points, viewed in ENNReal, is bounded by the volume of the nonnegative weighted simplex with height H plus the sum of the weights.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_expandedRegion_volume
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    ENNReal.ofReal ((strictWeightedSimplex w H).card : Real) ≤
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (∑ i, w i * x i) ≤ H + Finset.univ.sum w} := by sorry
