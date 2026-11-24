-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sqs_subgroupOf_self
-- name    : GlobalTheory.QNorm.sqs_subgroupOf_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:03:22.036777+00:00
-- url     : https://prove2.me/theorems/c8b3f8a7-b825-4205-937a-39d44854d646
-- title:
--   QNorm: sqs subgroup Of self
-- statement:
--   The QNorm construction uses the sqs subgroup Of self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberField.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberField.lean#L11-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
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

theorem GlobalTheory.QNorm.sqs_subgroupOf_self {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs U).subgroupOf U = sqs (⊤ : Subgroup U) := by sorry
