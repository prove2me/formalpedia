-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_explicit_sandwich
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_explicit_sandwich
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:32:46.353208+00:00
-- url     : https://prove2.me/theorems/47bdbf3a-edaa-43dd-bd8e-d8944c46df19
-- title:
--   Scaled cube bounds for the weighted simplex count
-- statement:
--   When H is positive and the lower cutoff A − (∑ᵢ wᵢ)/H is positive, the normalized lattice count lies between the explicit weighted-simplex volume expressions at cutoffs A − (∑ᵢ wᵢ)/H and A + (∑ᵢ wᵢ)/H.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_explicit_sandwich {m : Nat} (w : Fin m → Real) (A H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) (hcut : (∑ i : Fin m, w i) / H < A) :
    (A - (∑ i : Fin m, w i) / H) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i ≤
        ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ∧
      ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤
        (A + (∑ i : Fin m, w i) / H) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
