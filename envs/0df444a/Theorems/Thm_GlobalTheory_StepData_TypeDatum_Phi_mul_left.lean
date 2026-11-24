-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_mul_left
-- name    : GlobalTheory.StepData.TypeDatum.Phi_mul_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:13.952038+00:00
-- url     : https://prove2.me/theorems/9e91be0c-4563-4d6f-a750-3483fe208c15
-- title:
--   Type Datum: Phi mul left
-- statement:
--   The Type Datum construction uses the Phi mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1043-L1059
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1043-L1059

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
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a) {μ : kˣ →* ℂˣ}

theorem GlobalTheory.StepData.TypeDatum.Phi_mul_left (hμ : IsTame μ) (h : P.stepJ t) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ ((h : GL (a ⊕ t) k).val * x) = P.rho μ (P.corner h) * P.Phi t μ x := by sorry
