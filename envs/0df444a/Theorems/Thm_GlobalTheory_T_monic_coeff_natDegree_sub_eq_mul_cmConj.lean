-- Prove2me | Theorems.Thm_GlobalTheory_T_monic_coeff_natDegree_sub_eq_mul_cmConj
-- name    : GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:53:22.871658+00:00
-- url     : https://prove2.me/theorems/b0f9b1e9-e748-4c48-a9fe-e4b7494b398f
-- title:
--   T: monic coeff nat Degree sub eq mul cm Conj
-- statement:
--   The T construction uses the monic coeff nat Degree sub eq mul cm Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicCoeffNatDegreeSubEqMulCmConjStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicCoeffNatDegreeSubEqMulCmConjStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicCoeffNatDegreeSubEqMulCmConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicCoeffNatDegreeSubEqMulCmConjStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by sorry
