-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_relIndex_sqs_le_two_mul
-- name    : GlobalTheory.QNorm.relIndex_sqs_le_two_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:02.880657+00:00
-- url     : https://prove2.me/theorems/e23ed9d5-c751-4f96-83b3-0575fc8ca3af
-- title:
--   QNorm: rel Index sqs le two mul
-- statement:
--   The QNorm construction uses the rel Index sqs le two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresLeTwoMulOfSubgroup.lean#L31-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresLeTwoMulOfSubgroup.lean#L31-L69

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

theorem GlobalTheory.QNorm.relIndex_sqs_le_two_mul :
    ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 →
      (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 →
      (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by sorry
