-- Prove2me | Theorems.Thm_GlobalTheory_coeff_natDegree_sub_eq_of_roots_norm_one
-- name    : GlobalTheory.coeff_natDegree_sub_eq_of_roots_norm_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:53.615837+00:00
-- url     : https://prove2.me/theorems/9cedffdf-eff7-4239-9885-1f7931845195
-- title:
--   Global Theory: coeff nat Degree sub eq of roots norm one
-- statement:
--   The Global Theory construction uses the coeff nat Degree sub eq of roots norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicCoeffNatDegreeSubEqMulCmConj.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonicCoeffNatDegreeSubEqMulCmConj.lean#L6-L50

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

theorem GlobalTheory.coeff_natDegree_sub_eq_of_roots_norm_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ = 1) :
    ∀ i ≤ Q.natDegree, Q.coeff (Q.natDegree - i) = Q.coeff 0 * starRingEnd ℂ (Q.coeff i) := by sorry
