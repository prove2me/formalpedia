-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam_eq
-- name    : GlobalTheory.StepData.TypeDatum.step_lam_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:34.027045+00:00
-- url     : https://prove2.me/theorems/7959b20e-36f6-4ca9-b917-2c6c81c1fbd8
-- title:
--   Type Datum: step lam eq
-- statement:
--   The Type Datum construction uses the step lam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L272-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L272-L276

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

theorem GlobalTheory.StepData.TypeDatum.step_lam_eq (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (h : P.stepJ t) (g : P.J)
    (hg : (g : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁) (D : GL t k)
    (hD : D.val = (h : GL (a ⊕ t) k).val.toBlocks₂₂) :
    (P.step t μ hμ).lam h = P.lam g * μ (Matrix.GeneralLinearGroup.det D) := by sorry
