-- Prove2me | Theorems.Thm_GlobalTheory_T_polynomial_approx_uniqueness
-- name    : GlobalTheory.T.polynomial_approx_uniqueness
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:39.031806+00:00
-- url     : https://prove2.me/theorems/04c84fe4-9ef5-4bac-8c04-fefae5432851
-- title:
--   T: polynomial approx uniqueness
-- statement:
--   The T construction uses the polynomial approx uniqueness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolynomialApproxUniquenessStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolynomialApproxUniquenessStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxUniqueness
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxUniquenessStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.polynomial_approx_uniqueness : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), φ.Flat → (maximalIdeal A).map φ = maximalIdeal R → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A) → ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n := by sorry
