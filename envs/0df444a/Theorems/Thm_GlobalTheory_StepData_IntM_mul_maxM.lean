-- Prove2me | Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
-- name    : GlobalTheory.StepData.IntM.mul_maxM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:51.971359+00:00
-- url     : https://prove2.me/theorems/5a260cb3-6e14-4bae-a4d0-5b562a923642
-- title:
--   Int M: mul max M
-- statement:
--   The Int M construction uses the mul max M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L45-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable {l m n : Type*}

theorem GlobalTheory.StepData.IntM.mul_maxM [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : IntM M) (h' : MaxM M') :
    MaxM (M * M') := by sorry
