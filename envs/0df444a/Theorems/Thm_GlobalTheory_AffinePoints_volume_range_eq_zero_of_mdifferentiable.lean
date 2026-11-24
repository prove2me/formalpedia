-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_volume_range_eq_zero_of_mdifferentiable
-- name    : GlobalTheory.AffinePoints.volume_range_eq_zero_of_mdifferentiable
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:49.079403+00:00
-- url     : https://prove2.me/theorems/cbf1e336-9877-4e6c-b138-e261876ee24d
-- title:
--   Affine Points: volume range eq zero of mdifferentiable
-- statement:
--   The Affine Points construction uses the volume range eq zero of mdifferentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L45-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {d : ℕ}

theorem GlobalTheory.AffinePoints.volume_range_eq_zero_of_mdifferentiable {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [LindelofSpace M]
    (h : finrank ℂ E < d) {f : M → Fin d → ℂ} (hf : MDifferentiable I 𝓘(ℂ, Fin d → ℂ) f) :
    volume (range f) = 0 := by sorry
