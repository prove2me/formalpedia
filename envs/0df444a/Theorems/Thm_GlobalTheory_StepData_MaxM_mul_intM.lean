-- Prove2me | Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
-- name    : GlobalTheory.StepData.MaxM.mul_intM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:02.144813+00:00
-- url     : https://prove2.me/theorems/2875e695-918d-49ea-ad03-f84c0ec88251
-- title:
--   Max M: mul int M
-- statement:
--   The Max M construction uses the mul int M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L51-L55

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

theorem GlobalTheory.StepData.MaxM.mul_intM [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : MaxM M) (h' : IntM M') :
    MaxM (M * M') := by sorry
