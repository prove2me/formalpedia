-- Prove2me | Theorems.Thm_GlobalTheory_LevelLaw_last_steps_law
-- name    : GlobalTheory.LevelLaw.last_steps_law
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:02:53.598154+00:00
-- url     : https://prove2.me/theorems/168a15ca-8b17-52bb-a780-2835727d486a
-- title:
--   Level Law: last steps law
-- statement:
--   The Level Law construction uses the last steps law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ParahoricChainLastTwoStepsRootOfUnity.lean#L127-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ParahoricChainLastTwoStepsRootOfUnity.lean#L127-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ParahoricChainLastTwoStepsRootOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LevelLaw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.LevelLaw.last_steps_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), _root_.GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, _root_.GlobalTheory.SplitWeil.IsUnram (η j)) → ∀ g : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : _root_.GlobalTheory.StepData.XIx κ t (s + 1) → k) x, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by sorry
