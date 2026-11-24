-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TestFunctionFibreIntegral_integral_mem_SB
-- name    : GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:34.924826+00:00
-- url     : https://prove2.me/theorems/69c9f806-5a8a-4a40-90f1-a10314a1d13f
-- title:
--   Test Function Fibre Integral: integral mem SB
-- statement:
--   The Test Function Fibre Integral construction uses the integral mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PartialIntegralMemSchwartzBruhat.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PartialIntegralMemSchwartzBruhat.lean#L32-L48

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TestFunctionFibreIntegral

theorem GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
    [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
    [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B)
    [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B),
    (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by sorry
