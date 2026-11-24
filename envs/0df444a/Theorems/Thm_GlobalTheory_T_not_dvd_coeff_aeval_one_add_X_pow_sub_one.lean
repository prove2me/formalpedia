-- Prove2me | Theorems.Thm_GlobalTheory_T_not_dvd_coeff_aeval_one_add_X_pow_sub_one
-- name    : GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:49.999439+00:00
-- url     : https://prove2.me/theorems/e053516f-ed9b-43fd-9f7f-2d1d1407b1f5
-- title:
--   T: not dvd coeff aeval one add X pow sub one
-- statement:
--   The T construction uses the not dvd coeff aeval one add X pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOneStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOneStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotDvdCoeffAevalOneAddXPowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotDvdCoeffAevalOneAddXPowSubOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by sorry
