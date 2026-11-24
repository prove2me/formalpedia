-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_relIndex_le_two_of_coset
-- name    : GlobalTheory.QNorm.relIndex_le_two_of_coset
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:01:53.567955+00:00
-- url     : https://prove2.me/theorems/d6807d37-8f4f-4fb5-9b4c-ab43e075364c
-- title:
--   QNorm: rel Index le two of coset
-- statement:
--   The QNorm construction uses the rel Index le two of coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresLeTwoMulOfSubgroup.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresLeTwoMulOfSubgroup.lean#L8-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresLeTwoMulOfSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.relIndex_le_two_of_coset {G : Type} [CommGroup G] (H K : Subgroup G) (ε : G)
    (h : ∀ x ∈ K, x ∈ H ∨ x * ε⁻¹ ∈ H) : H.relIndex K ≤ 2 := by sorry
