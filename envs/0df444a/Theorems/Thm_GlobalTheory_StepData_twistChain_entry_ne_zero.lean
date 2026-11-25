-- Prove2me | Theorems.Thm_GlobalTheory_StepData_twistChain_entry_ne_zero
-- name    : GlobalTheory.StepData.twistChain_entry_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:20.874796+00:00
-- url     : https://prove2.me/theorems/04b005f3-799e-4f4a-a605-2fd14fe6eeb9
-- title:
--   Step Data: twist Chain entry ne zero
-- statement:
--   The Step Data construction uses the twist Chain entry ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1228-L1278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1228-L1278

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
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.StepData.twistChain_entry_ne_zero [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    (ν : Measure k) [ν.IsAddHaarMeasure] (κ t : Type*) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
    (s c : ℕ) (h : 0 + 1 + c = s) :
    DoubleCoset.mk _ _ 1 ∈ (twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1).idx ψ ν 0 c h 1 ∧
      (twistChain s t κ (1 : kˣ →* ℂˣ) (fun _ _ => rfl) fun _ => 1).entry ψ ν 0 c h 1 1 ≠ 0 := by sorry
