-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_intM_of_Phi_ne_zero
-- name    : GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:02.2109+00:00
-- url     : https://prove2.me/theorems/01fd1bf1-be86-4ce5-8ea5-49e6178b526a
-- title:
--   Type Datum: int M of Phi ne zero
-- statement:
--   The Type Datum construction uses the int M of Phi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L321-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L321-L326

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
omit [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero (μ : kˣ →* ℂˣ) {x : Matrix (a ⊕ t) a k} (h : P.Phi t μ x ≠ 0) : IntM x := by sorry
