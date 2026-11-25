-- Prove2me | Theorems.Thm_GlobalTheory_StepData_integrable_hat
-- name    : GlobalTheory.StepData.integrable_hat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:38.687321+00:00
-- url     : https://prove2.me/theorems/e94dbcdb-584d-4219-8340-074130a03e2e
-- title:
--   Step Data: integrable hat
-- statement:
--   The Step Data construction uses the integrable hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L805-L810
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L805-L810

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

theorem GlobalTheory.StepData.integrable_hat [ν.IsAddHaarMeasure] (hψ : Continuous ψ) {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (η : n → k) : Integrable (fun y => f y * (ψ (ε * (η ⬝ᵥ y)) : ℂ)) (Measure.pi fun _ => ν) := by sorry
