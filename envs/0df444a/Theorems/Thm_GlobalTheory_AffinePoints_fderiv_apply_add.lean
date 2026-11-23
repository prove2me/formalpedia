-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_add
-- name    : GlobalTheory.AffinePoints.fderiv_apply_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:49.949823+00:00
-- url     : https://prove2.me/theorems/e3752e8b-6588-4adb-b8e4-2d1eb9a1759b
-- title:
--   Affine Points: fderiv apply add
-- statement:
--   The Affine Points construction uses the fderiv apply add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L316-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L316-L321

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
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}

theorem GlobalTheory.AffinePoints.fderiv_apply_add {z : E} (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E)
    (a b : A) : fderiv ℂ (fun z => φ z (a + b)) z v =
      fderiv ℂ (fun z => φ z a) z v + fderiv ℂ (fun z => φ z b) z v := by sorry
