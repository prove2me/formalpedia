-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_fderiv_apply_eq_zero_of_mem_adjoin
-- name    : GlobalTheory.AffinePoints.fderiv_apply_eq_zero_of_mem_adjoin
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:43.258877+00:00
-- url     : https://prove2.me/theorems/66670308-9fee-49b9-ba67-2ee2de8bd21d
-- title:
--   Affine Points: fderiv apply eq zero of mem adjoin
-- statement:
--   The Affine Points construction uses the fderiv apply eq zero of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L323-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L323-L331

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

theorem GlobalTheory.AffinePoints.fderiv_apply_eq_zero_of_mem_adjoin {z : E}
    (hφ : ∀ a, DifferentiableAt ℂ (fun z => φ z a) z) (v : E) {s : Set A}
    (hs : ∀ a ∈ s, fderiv ℂ (fun z => φ z a) z v = 0) {a : A} (ha : a ∈ Algebra.adjoin ℂ s) :
    fderiv ℂ (fun z => φ z a) z v = 0 := by sorry
