-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_eq_zero_pi
-- name    : GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:10.533789+00:00
-- url     : https://prove2.me/theorems/54ff8b48-2ea5-4163-b306-9ada6a1f2473
-- title:
--   Fourier Pi: fourier eq zero pi
-- statement:
--   The Fourier Pi construction uses the fourier eq zero pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L60-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L60-L82

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

theorem GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) {s : kˣ}
    {f : (n → k) → ℂ} (hs : ∀ t ∈ box n s, ∀ x, f (x + t) = f x) {y : n → k} (hy : y ∉ box n (c * s⁻¹)) :
    ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by sorry
