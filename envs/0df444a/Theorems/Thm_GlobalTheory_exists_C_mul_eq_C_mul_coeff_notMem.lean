-- Prove2me | Theorems.Thm_GlobalTheory_exists_C_mul_eq_C_mul_coeff_notMem
-- name    : GlobalTheory.exists_C_mul_eq_C_mul_coeff_notMem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:00.526291+00:00
-- url     : https://prove2.me/theorems/6aae6687-e69e-4bd0-b83c-62cd818c7e2e
-- title:
--   Global Theory: exists C mul eq C mul coeff not Mem
-- statement:
--   The Global Theory construction uses the exists C mul eq C mul coeff not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L160-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L160-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.exists_C_mul_eq_C_mul_coeff_notMem {ι o : Type*} [CommRing o] [IsDedekindDomain o]
    {J : Ideal o} (hJ : J ≠ ⊤) {G : MvPolynomial ι o} (hG : G ≠ 0) :
    ∃ (b u : o) (G' : MvPolynomial ι o), b ≠ 0 ∧ C b * G' = C u * G ∧ ∃ m, G'.coeff m ∉ J := by sorry
