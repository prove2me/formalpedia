-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_relIndex_sqs_sUnits
-- name    : GlobalTheory.QNorm.relIndex_sqs_sUnits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:56.031795+00:00
-- url     : https://prove2.me/theorems/7f2d711d-b3d4-4258-a8fe-23a29665ba54
-- title:
--   QNorm: rel Index sqs s Units
-- statement:
--   The QNorm construction uses the rel Index sqs s Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberField.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberField.lean#L43-L47

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

theorem GlobalTheory.QNorm.relIndex_sqs_sUnits : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by sorry
