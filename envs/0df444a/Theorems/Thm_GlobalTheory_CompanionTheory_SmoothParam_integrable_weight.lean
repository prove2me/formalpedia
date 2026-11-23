-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_integrable_weight
-- name    : GlobalTheory.CompanionTheory.SmoothParam.integrable_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:11.791715+00:00
-- url     : https://prove2.me/theorems/dca3b15b-0917-4cdd-84c4-3befcd9f75f9
-- title:
--   Smooth Param: integrable weight
-- statement:
--   The Smooth Param construction uses the integrable weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L34-L46

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
omit [FiniteDimensional ℝ P] [NormedSpace ℝ P] [FiniteDimensional ℝ Y] [NormedSpace ℝ Y]

theorem GlobalTheory.CompanionTheory.SmoothParam.integrable_weight {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) {H : P × Y → F} (hH : Continuous H) (p : P) :
    Integrable (fun x => u x • H (p, ψ x)) ν := by sorry
