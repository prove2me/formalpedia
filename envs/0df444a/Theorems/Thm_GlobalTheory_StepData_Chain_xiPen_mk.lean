-- Prove2me | Theorems.Thm_GlobalTheory_StepData_Chain_xiPen_mk
-- name    : GlobalTheory.StepData.Chain.xiPen_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:21.842133+00:00
-- url     : https://prove2.me/theorems/1f9a42ac-b23e-495b-aa86-c071595ce6de
-- title:
--   Chain: xi Pen mk
-- statement:
--   The Chain construction uses the xi Pen mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L911-L915
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L911-L915

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
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
open GlobalTheory.StepData.Chain
variable (T : Chain k s X Z)
variable (A : RepFam k s X)
variable (S M : Submodule 𝒪[k] (X (s + 1) → k))
variable {T A S M}

theorem GlobalTheory.StepData.Chain.xiPen_mk (H : T.Adapted A S M) {g : GL (X s ⊕ Fin (0 + 1)) k} (hg : g ∈ A s 0 rfl) (y : X (s + 1) → k)
    (x₀ : Matrix (X (s + 1)) (X s) k) : T.xiPen M g (Submodule.Quotient.mk y) x₀ = T.Psi g x₀ y := by sorry
