-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_isOpen_fderiv_eq_zero
-- name    : GlobalTheory.AffinePoints.exists_isOpen_fderiv_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:28.444804+00:00
-- url     : https://prove2.me/theorems/fb0b6233-fffd-4cd1-9f77-5205b1450bad
-- title:
--   Affine Points: exists is Open fderiv eq zero
-- statement:
--   The Affine Points construction uses the exists is Open fderiv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L350-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L350-L384

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

theorem GlobalTheory.AffinePoints.exists_isOpen_fderiv_eq_zero {R : Type*} [CommRing R] (g : R →+* A) {a : A}
    (ha : g.IsIntegralElem a) (hU : IsOpen U) (hne : U.Nonempty)
    (hφ : ∀ a, DifferentiableOn ℂ (fun z => φ z a) U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, ∀ v,
      (∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) → fderiv ℂ (fun z => φ z a) z v = 0 := by sorry
