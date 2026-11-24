-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_isAlgebraicChart_of_isSmoothAt
-- name    : GlobalTheory.AffinePoints.exists_isAlgebraicChart_of_isSmoothAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:55:05.029164+00:00
-- url     : https://prove2.me/theorems/7c2581ef-f35e-49b8-ae77-419426e19b14
-- title:
--   Affine Points: exists is Algebraic Chart of is Smooth At
-- statement:
--   The Affine Points construction uses the exists is Algebraic Chart of is Smooth At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L258-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L258-L265

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

theorem GlobalTheory.AffinePoints.exists_isAlgebraicChart_of_isSmoothAt [IsDomain A] [Algebra.FiniteType ℂ A]
    (hd : ringKrullDim A = d) (p : A →ₐ[ℂ] ℂ)
    (hp : haveI := RingHom.ker_isPrime p; Algebra.IsSmoothAt ℂ (RingHom.ker p)) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), IsAlgebraicChart e ∧ p ∈ e.source := by sorry
