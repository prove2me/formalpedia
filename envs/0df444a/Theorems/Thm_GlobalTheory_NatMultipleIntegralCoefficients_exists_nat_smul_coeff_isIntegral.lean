-- Prove2me | Theorems.Thm_GlobalTheory_NatMultipleIntegralCoefficients_exists_nat_smul_coeff_isIntegral
-- name    : GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:51.939805+00:00
-- url     : https://prove2.me/theorems/c7bb36fe-6209-45bf-973a-815692d935ea
-- title:
--   Nat Multiple Integral Coefficients: exists nat smul coeff is Integral
-- statement:
--   The Nat Multiple Integral Coefficients construction uses the exists nat smul coeff is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatSmulCoeffIsIntegral.lean#L5-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatSmulCoeffIsIntegral.lean#L5-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNatSmulCoeffIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMultipleIntegralCoefficients

theorem GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : σ →₀ ℕ, IsIntegral ℤ (MvPolynomial.coeff m ((N : K) • P)) := by sorry
