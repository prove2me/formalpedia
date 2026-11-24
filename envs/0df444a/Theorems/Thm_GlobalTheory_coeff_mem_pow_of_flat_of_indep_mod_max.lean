-- Prove2me | Theorems.Thm_GlobalTheory_coeff_mem_pow_of_flat_of_indep_mod_max
-- name    : GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:46.589662+00:00
-- url     : https://prove2.me/theorems/3d07e51f-ba98-4f0b-a319-e683074b0781
-- title:
--   Global Theory: coeff mem pow of flat of indep mod max
-- statement:
--   The Global Theory construction uses the coeff mem pow of flat of indep mod max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolynomialApproxUniqueness.lean#L64-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolynomialApproxUniqueness.lean#L64-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsLocalRing TensorProduct

theorem GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), φ.Flat → (maximalIdeal A).map φ = maximalIdeal R → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A) → ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n := by sorry
