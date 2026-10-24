-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_encoded_not_support_coeff_zero
-- name    : OAI.PiExponent.DeterminantContradiction.encoded_not_support_coeff_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:32:31.289779+00:00
-- url     : https://prove2.me/theorems/67c4fbd9-d4ed-4163-afb3-2a50aed236f9
-- title:
--   A coefficient vanishes outside the encoded support
-- statement:
--   If a finite-function index is outside the finite-function encoding of a polynomial's support, then its corresponding polynomial coefficient is zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.encoded_not_support_coeff_zero
    (m : Nat) (P : MvPolynomial (Fin m) Complex)
    (a : Fin m → Nat)
    (h : a ∉ P.support.map Finsupp.equivFunOnFinite.toEmbedding) :
    P.coeff (InterpolationMatrix.exponentVector a) = 0 := by sorry
