-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_IsAlgebraicChart_volume_image_zeroSet
-- name    : GlobalTheory.AffinePoints.IsAlgebraicChart.volume_image_zeroSet
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:54:17.5922+00:00
-- url     : https://prove2.me/theorems/c5628a09-9601-4913-8b8b-d0db8c8196f6
-- title:
--   Is Algebraic Chart: volume image zero Set
-- statement:
--   The Is Algebraic Chart construction uses the volume image zero Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L205-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L205-L256

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

theorem GlobalTheory.AffinePoints.IsAlgebraicChart.volume_image_zeroSet [IsDomain A] [Algebra.FiniteType ℂ A]
    (hd : ringKrullDim A = d) {e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ)}
    (he : IsAlgebraicChart e) {f : A} (hf : f ≠ 0) :
    volume (e '' (e.source ∩ {p | p f = 0})) = 0 := by sorry
