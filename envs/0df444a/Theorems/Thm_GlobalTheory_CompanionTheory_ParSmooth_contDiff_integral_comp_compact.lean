-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ParSmooth_contDiff_integral_comp_compact
-- name    : GlobalTheory.CompanionTheory.ParSmooth.contDiff_integral_comp_compact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:10.351545+00:00
-- url     : https://prove2.me/theorems/e9b3362e-0bc7-4c58-ba9b-1bdb453c3be4
-- title:
--   Par Smooth: cont Diff integral comp compact
-- statement:
--   The Par Smooth construction uses the cont Diff integral comp compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/JetProofs/ContinuousIteratedFDerivPartial.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/JetProofs/ContinuousIteratedFDerivPartial.lean#L30-L42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_JetProofs_ContinuousIteratedFDerivPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ParSmooth

theorem GlobalTheory.CompanionTheory.ParSmooth.contDiff_integral_comp_compact {P Q E β : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace β] [T2Space β]
    [SecondCountableTopology β] [CompactSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (Ψ : P × Q → E) (hΨ : ContDiff ℝ ∞ Ψ) (q : β → Q)
    (hq : Continuous q) : ContDiff ℝ ∞ fun y => ∫ a, Ψ (y, q a) ∂ν := by sorry
