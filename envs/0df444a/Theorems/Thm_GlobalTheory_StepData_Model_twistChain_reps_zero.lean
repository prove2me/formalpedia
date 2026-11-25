-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Model_twistChain_reps_zero
-- name    : GlobalTheory.StepData.Model.twistChain_reps_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:32.997525+00:00
-- url     : https://prove2.me/theorems/cf120330-8f70-5bfb-9cff-0731b9615b11
-- title:
--   Model: twist Chain reps zero
-- statement:
--   The Model construction uses the twist Chain reps zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L305-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L305-L323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
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
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.Model.twistChain_reps_zero [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ)
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν' : ℕ → kˣ →* ℂˣ) :
    let T := twistChain 0 t κ δ hδ ν'
    let A : RepFam k 0 (XIx κ t) := fun _ _ _ => {1}
    T.IsRepSystem A ψ ν ∧ T.RepsInStab A ∧ T.RepsMeet A ∧ T.RepsNormal A ϖ ∧ T.RepsOne A := by sorry
