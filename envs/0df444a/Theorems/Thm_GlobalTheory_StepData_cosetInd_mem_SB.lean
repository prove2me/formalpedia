-- Prove2me | Theorems.Thm_GlobalTheory_StepData_cosetInd_mem_SB
-- name    : GlobalTheory.StepData.cosetInd_mem_SB
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:05.606388+00:00
-- url     : https://prove2.me/theorems/aeac9a87-3242-49cf-b901-538309a0f972
-- title:
--   Step Data: coset Ind mem SB
-- statement:
--   The Step Data construction uses the coset Ind mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L814-L826
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L814-L826

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
variable {k : Type*} [Field k] {n n' : Type*}
variable [ValuativeRel k]
variable [Fintype n] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k)
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.StepData.cosetInd_mem_SB (c : kˣ) (yb : (n → k) ⧸ box n c) : cosetInd (box n c) yb ∈ SB (n → k) := by sorry
