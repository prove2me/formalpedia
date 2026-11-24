-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_pi_of_conductor
-- name    : GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:36.123287+00:00
-- url     : https://prove2.me/theorems/65ec310d-6ea7-43ed-8b55-4f8645d24c5a
-- title:
--   Fourier Pi: fourier pi of conductor
-- statement:
--   The Fourier Pi construction uses the fourier pi of conductor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L199-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L199-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧
      ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by sorry
