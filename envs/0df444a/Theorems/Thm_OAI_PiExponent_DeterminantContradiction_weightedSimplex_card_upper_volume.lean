-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_upper_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:39:31.429969+00:00
-- url     : https://prove2.me/theorems/0c3ef681-025a-4f97-8902-c6909223afcb
-- title:
--   Upper volume bound for the weighted simplex count
-- statement:
--   The normalized count is at most the volume of the simplex expanded by the sum of the coordinate box widths. Each lattice point contributes a box of volume `∏ i, w i`; for `m = 0`, both sides are 1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_volume {m : Nat} (w : Fin m → Real) (A H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) (hcut : (∑ i : Fin m, w i) / H < A) :
    ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤
      (A + (∑ i : Fin m, w i) / H) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
