-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mem_SB_of_periodic
-- name    : GlobalTheory.StepData.mem_SB_of_periodic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:36.056495+00:00
-- url     : https://prove2.me/theorems/1584fb0a-10a6-43b5-a08a-59c5799da5fb
-- title:
--   Step Data: mem SB of periodic
-- statement:
--   The Step Data construction uses the mem SB of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L332-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L332-L341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
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
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
omit [DecidableEq a] [DecidableEq b]

theorem GlobalTheory.StepData.mem_SB_of_periodic {f : Matrix b a k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, MaxM y → f (x + y) = f x) : f ∈ SB (Matrix b a k) := by sorry
