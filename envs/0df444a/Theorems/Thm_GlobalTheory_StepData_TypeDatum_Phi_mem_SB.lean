-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_mem_SB
-- name    : GlobalTheory.StepData.TypeDatum.Phi_mem_SB
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:21.51783+00:00
-- url     : https://prove2.me/theorems/2e1932bf-866e-4780-9f70-ba677ae881d9
-- title:
--   Type Datum: Phi mem SB
-- statement:
--   The Type Datum construction uses the Phi mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L344-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L344-L346

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
omit [DecidableEq t]

theorem GlobalTheory.StepData.TypeDatum.Phi_mem_SB (P : TypeDatum k a) {μ : kˣ →* ℂˣ} (hμ : IsTame μ) :
    P.Phi t μ ∈ SB (Matrix (a ⊕ t) a k) := by sorry
