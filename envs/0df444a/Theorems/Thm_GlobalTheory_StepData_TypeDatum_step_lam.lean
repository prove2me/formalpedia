-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam
-- name    : GlobalTheory.StepData.TypeDatum.step_lam
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:26.587816+00:00
-- url     : https://prove2.me/theorems/798d3f3f-9988-4b09-a83c-1be2e7acf67e
-- title:
--   Type Datum: step lam
-- statement:
--   The Type Datum construction uses the step lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L265-L270

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
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a)

theorem GlobalTheory.StepData.TypeDatum.step_lam (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (h : P.stepJ t) (g : P.J)
    (hg : (g : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁) :
    (P.step t μ hμ).lam h = P.lam g * (μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k)) := by sorry
