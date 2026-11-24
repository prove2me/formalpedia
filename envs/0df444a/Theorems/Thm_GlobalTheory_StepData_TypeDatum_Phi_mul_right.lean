-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_mul_right
-- name    : GlobalTheory.StepData.TypeDatum.Phi_mul_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:10.491823+00:00
-- url     : https://prove2.me/theorems/25914ce8-7511-4c57-92e1-ff47ac0fe137
-- title:
--   Type Datum: Phi mul right
-- statement:
--   The Type Datum construction uses the Phi mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1034-L1041
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1034-L1041

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
omit [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.TypeDatum.Phi_mul_right (g : P.J) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ (x * (g : GL a k).val) = P.rho μ g * P.Phi t μ x := by sorry
