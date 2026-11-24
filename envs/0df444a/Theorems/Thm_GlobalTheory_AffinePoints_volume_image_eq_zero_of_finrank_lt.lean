-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_volume_image_eq_zero_of_finrank_lt
-- name    : GlobalTheory.AffinePoints.volume_image_eq_zero_of_finrank_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:33.302678+00:00
-- url     : https://prove2.me/theorems/942c9230-75eb-41d0-9298-3dd662cee789
-- title:
--   Affine Points: volume image eq zero of finrank lt
-- statement:
--   The Affine Points construction uses the volume image eq zero of finrank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L38-L43

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

theorem GlobalTheory.AffinePoints.volume_image_eq_zero_of_finrank_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : finrank ℂ E < d) {s : Set E} {f : E → Fin d → ℂ}
    (hf : DifferentiableOn ℂ f s) : volume (f '' s) = 0 := by sorry
