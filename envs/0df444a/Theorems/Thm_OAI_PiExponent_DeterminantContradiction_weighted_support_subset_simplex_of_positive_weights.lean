-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_subset_simplex_of_positive_weights
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_support_subset_simplex_of_positive_weights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:36:12.737456+00:00
-- url     : https://prove2.me/theorems/5267fe6f-9970-4125-96ad-23c91c61b27a
-- title:
--   Positive weighted support is contained in its finite simplex
-- statement:
--   For any finite list of strictly positive real weights, every function-index encoding of a monomial exponent in a polynomial whose support has weighted degree at most H belongs to the inclusive finite weighted simplex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.weighted_support_subset_simplex_of_positive_weights {n : Nat} (w : Fin n → Real) (H : Real) (hw : ∀ i, 0 < w i) (P : {Q : MvPolynomial (Fin n) Complex // ∀ a ∈ Q.support, ∑ i, w i * (a i : Real) ≤ H}) : P.1.support.map Finsupp.equivFunOnFinite.toEmbedding ⊆ realWeightedSimplex w H := by sorry
