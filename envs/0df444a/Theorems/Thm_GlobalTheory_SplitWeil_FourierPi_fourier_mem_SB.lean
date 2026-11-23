-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_mem_SB
-- name    : GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:42.823803+00:00
-- url     : https://prove2.me/theorems/2632ed5f-69be-481a-af30-06e31ec3e135
-- title:
--   Fourier Pi: fourier mem SB
-- statement:
--   The Fourier Pi construction uses the fourier mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L116-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L116-L136

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

theorem GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) := by sorry
