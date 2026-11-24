-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_weight
-- name    : GlobalTheory.CompanionTheory.SmoothParam.contDiff_weight
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:56.663386+00:00
-- url     : https://prove2.me/theorems/4090e2a5-cb95-40df-8c3e-a2f7869055fa
-- title:
--   Smooth Param: cont Diff weight
-- statement:
--   The Smooth Param construction uses the cont Diff weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L97-L101

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem GlobalTheory.CompanionTheory.SmoothParam.contDiff_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) [CompleteSpace F] {H : P × Y → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p => ∫ x, u x • H (p, ψ x) ∂ν) := by sorry
