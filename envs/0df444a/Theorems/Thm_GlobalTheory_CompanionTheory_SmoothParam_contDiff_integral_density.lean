-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_integral_density
-- name    : GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:40.244791+00:00
-- url     : https://prove2.me/theorems/c1c04020-1fed-5f44-95aa-15a07aee3dfa
-- title:
--   Smooth Param: cont Diff integral density
-- statement:
--   The Smooth Param construction uses the cont Diff integral density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L103-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L103-L150

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

theorem GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density (Ω P Y : Type) [MeasurableSpace Ω] [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (ν : Measure Ω) (w : Ω → ℂ) (ψ : Ω → Y) (K : Set Y)
    (hw : Integrable w ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (h : P × Y → ℂ) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p => ∫ x, h (p, ψ x) * w x ∂ν) ∧
      ∀ p v, fderiv ℝ (fun q => ∫ x, h (q, ψ x) * w x ∂ν) p v
        = ∫ x, fderiv ℝ (fun q => h (q, ψ x)) p v * w x ∂ν := by sorry
