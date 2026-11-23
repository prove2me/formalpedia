-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_indicator_pi
-- name    : GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:59.311008+00:00
-- url     : https://prove2.me/theorems/eec7dde9-93bb-49a1-8622-aa0f9b9c30c1
-- title:
--   Fourier Pi: fourier indicator pi
-- statement:
--   The Fourier Pi construction uses the fourier indicator pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L84-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L84-L114

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

theorem GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) (s : kˣ)
    (x : n → k) :
    ∫ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) ∂μ =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x := by sorry
