-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_rank_le_of_immersion
-- name    : GlobalTheory.AffinePoints.rank_le_of_immersion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:56.935011+00:00
-- url     : https://prove2.me/theorems/9e217fd6-67a0-4623-9ac6-986fe811a76d
-- title:
--   Affine Points: rank le of immersion
-- statement:
--   The Affine Points construction uses the rank le of immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L386-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L386-L423

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

theorem GlobalTheory.AffinePoints.rank_le_of_immersion [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hU : IsOpen U) (hne : U.Nonempty) (hφ : ∀ a, DifferentiableOn ℂ (fun z => φ z a) U)
    (himm : ∀ z ∈ U, ∀ v, (∀ a, fderiv ℂ (fun z => φ z a) z v = 0) → v = 0) :
    Module.rank ℂ E ≤ d := by sorry
