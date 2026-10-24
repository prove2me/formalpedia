-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_ge_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_ge_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:44:24.199099+00:00
-- url     : https://prove2.me/theorems/e5b3709f-5243-4716-ac48-51819382643c
-- title:
--   Weighted simplex count dominates contracted simplex volume
-- statement:
--   For positive coordinate weights and a radius strictly larger than their sum, the number of nonnegative integer vectors with weighted sum at most the radius is at least the volume of the simplex whose radius is reduced by one unit in each coordinate. The floor-box covering argument gives a proof route, with the empty-dimensional case interpreted using empty products.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_ge_volume {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (R - ∑ i : Fin m, w i) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i ≤
      ((realWeightedSimplex w R).card : Real) := by sorry
