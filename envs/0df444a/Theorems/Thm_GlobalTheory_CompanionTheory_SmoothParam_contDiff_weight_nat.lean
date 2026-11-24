-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_weight_nat
-- name    : GlobalTheory.CompanionTheory.SmoothParam.contDiff_weight_nat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:41.292263+00:00
-- url     : https://prove2.me/theorems/4490e0db-ee37-4ee2-89a7-b7bf76f720d8
-- title:
--   Smooth Param: cont Diff weight nat
-- statement:
--   The Smooth Param construction uses the cont Diff weight nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L74-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L74-L95

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

theorem GlobalTheory.CompanionTheory.SmoothParam.contDiff_weight_nat {ν : Measure Ω} {u : Ω → ℝ} {ψ : Ω → Y} {K : Set Y}
    (hu : Integrable u ν) (hψ : AEStronglyMeasurable ψ ν) (hK : IsCompact K)
    (hψK : ∀ᵐ x ∂ν, ψ x ∈ K) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : P × Y → F),
      ContDiff ℝ ∞ H → ContDiff ℝ n (fun p => ∫ x, u x • H (p, ψ x) ∂ν) := by sorry
