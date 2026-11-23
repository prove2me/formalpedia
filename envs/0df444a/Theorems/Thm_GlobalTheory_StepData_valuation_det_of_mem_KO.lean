-- Prove2me | Theorems.Thm_GlobalTheory_StepData_valuation_det_of_mem_KO
-- name    : GlobalTheory.StepData.valuation_det_of_mem_KO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:13.248796+00:00
-- url     : https://prove2.me/theorems/247bb597-712c-4ba5-8d84-214dea6821ea
-- title:
--   Step Data: valuation det of mem KO
-- statement:
--   The Step Data construction uses the valuation det of mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L123-L129

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
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.StepData.valuation_det_of_mem_KO {g : GL n k} (h : g ∈ KO k n) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by sorry
