-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_normalize_expanded_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_normalize_expanded_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:05:59.623978+00:00
-- url     : https://prove2.me/theorems/3c4f83aa-6b3b-4783-ae5d-a3f2dc9e01b9
-- title:
--   Normalize the expanded volume estimate
-- statement:
--   Normalize the unscaled count bound using positivity and the identity A * H + ∑ w = H * (A + (∑ w) / H). The hypotheses are retained exactly; hcut ensures the scale A * H is positive, including the zero-dimensional boundary case. This removes only the algebraic rescaling from the parent. An independent proof route is to derive nonnegativity of the weight sum, establish 0 < A, rewrite the identity using field_simp with hH.ne', and combine the resulting power identity with hcard and positivity of H.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_normalize_expanded_bound {m : Nat} (w : Fin m → Real) (A H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) (hcut : (∑ i : Fin m, w i) / H < A)
    (hcard : ((OAI.PiExponent.realWeightedSimplex w (A * H)).card : Real) ≤
      (A * H + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) :
    ((OAI.PiExponent.realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤
      (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
