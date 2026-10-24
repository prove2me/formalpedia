-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_lower_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:39:03.824974+00:00
-- url     : https://prove2.me/theorems/54b685a3-f8fa-4df6-8232-4058265895d2
-- title:
--   Lower volume bound for the weighted simplex count
-- statement:
--   The normalized count is at least the volume of the simplex contracted by the sum of the coordinate box widths. The strict cutoff hypothesis ensures this contracted radius is positive. For `m = 0`, both sides are 1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_volume {m : Nat} (w : Fin m → Real) (A H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) (hcut : (∑ i : Fin m, w i) / H < A) :
    (A - (∑ i : Fin m, w i) / H) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i ≤
      ((realWeightedSimplex w (A * H)).card : Real) / H ^ m := by sorry
