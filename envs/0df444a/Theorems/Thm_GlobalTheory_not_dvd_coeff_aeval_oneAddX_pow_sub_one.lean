-- Prove2me | Theorems.Thm_GlobalTheory_not_dvd_coeff_aeval_oneAddX_pow_sub_one
-- name    : GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:44.608993+00:00
-- url     : https://prove2.me/theorems/3f55da12-30a6-48c7-9dd2-015654ca0b98
-- title:
--   Global Theory: not dvd coeff aeval one Add X pow sub one
-- statement:
--   The Global Theory construction uses the not dvd coeff aeval one Add X pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOne.lean#L38-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOne.lean#L38-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotDvdCoeffAevalOneAddXPowSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open scoped BigOperators

theorem GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by sorry
