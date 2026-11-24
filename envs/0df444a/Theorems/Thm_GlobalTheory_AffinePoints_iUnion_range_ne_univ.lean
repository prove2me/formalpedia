-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_iUnion_range_ne_univ
-- name    : GlobalTheory.AffinePoints.iUnion_range_ne_univ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:46.498538+00:00
-- url     : https://prove2.me/theorems/3b2d8894-575e-426d-bdb6-2ec69fef57e7
-- title:
--   Affine Points: i Union range ne univ
-- statement:
--   The Affine Points construction uses the i Union range ne univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L288-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L288-L295

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
variable {ι : Type*} [Countable ι] {E H M : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℂ (E i) (H i)} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]

theorem GlobalTheory.AffinePoints.iUnion_range_ne_univ [Algebra.FiniteType ℂ A] (hd : ringKrullDim A = d)
    (hE : ∀ i, finrank ℂ (E i) < d) (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ))
    (hφ : ∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) : ⋃ i, range (φ i) ≠ univ := by sorry
