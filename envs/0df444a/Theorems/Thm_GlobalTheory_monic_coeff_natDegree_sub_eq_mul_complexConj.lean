-- Prove2me | Theorems.Thm_GlobalTheory_monic_coeff_natDegree_sub_eq_mul_complexConj
-- name    : GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:05.49752+00:00
-- url     : https://prove2.me/theorems/a0ca12cc-5e32-441d-bacf-a34acba8de5b
-- title:
--   Global Theory: monic coeff nat Degree sub eq mul complex Conj
-- statement:
--   The Global Theory construction uses the monic coeff nat Degree sub eq mul complex Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicCoeffNatDegreeSubEqMulCmConj.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicCoeffNatDegreeSubEqMulCmConj.lean#L52-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicCoeffNatDegreeSubEqMulCmConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory

theorem GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by sorry
