-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_PartialFourier_partial_fourier_inversion
-- name    : GlobalTheory.LocFlat.PartialFourier.partial_fourier_inversion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:21.838723+00:00
-- url     : https://prove2.me/theorems/a352f9f7-88bd-416f-9587-b6356e431fea
-- title:
--   Partial Fourier: partial fourier inversion
-- statement:
--   The Partial Fourier construction uses the partial fourier inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialFourierInversion.lean#L55-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialFourierInversion.lean#L55-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialFourierInversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PartialFourier
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.LocFlat.PartialFourier.partial_fourier_inversion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I : Type) [Fintype I], ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : I → k), ∀ f ∈ SB ((I → k) × (J → k)), Integrable (fun l : I → k => ∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) (Measure.pi fun _ => ν) ∧ ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν) = (C : ℂ) * ∫ y : J → k, f (a, y) ∂(Measure.pi fun _ => ν) := by sorry
