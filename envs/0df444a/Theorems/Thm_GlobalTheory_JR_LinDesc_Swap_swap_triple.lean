-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_swap_triple
-- name    : GlobalTheory.JR.LinDesc.Swap.swap_triple
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:07.234024+00:00
-- url     : https://prove2.me/theorems/1a340b0d-8336-40ba-a706-4055bd5112d7
-- title:
--   Swap: swap triple
-- statement:
--   The Swap construction uses the swap triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L90-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L90-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap

theorem GlobalTheory.JR.LinDesc.Swap.swap_triple {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    [SigmaFinite ν] (k : X → Y → Y → ℂ) (hk : Continuous (fun z : (Y × Y) × X => k z.2 z.1.1 z.1.2))
    (S : Set X) (B C : Set Y) (hS : IsCompact S) (hB : IsCompact B) (hC : IsCompact C)
    (hsupp : ∀ g b c, k g b c ≠ 0 → g ∈ S ∧ b ∈ B ∧ c ∈ C) :
    ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ b, ∫ c, ∫ g, k g b c ∂μ ∂ν ∂ν := by sorry
