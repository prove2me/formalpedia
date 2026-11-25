-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_complexPoints_manifold_and_dimension
-- name    : GlobalTheory.AffinePoints.complexPoints_manifold_and_dimension
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:15.688768+00:00
-- url     : https://prove2.me/theorems/c3898d7e-313b-4d4a-9741-dedb907ed41b
-- title:
--   Affine Points: complex Points manifold and dimension
-- statement:
--   The Affine Points construction uses the complex Points manifold and dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L427-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L427-L462

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

theorem GlobalTheory.AffinePoints.complexPoints_manifold_and_dimension (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (d : ℕ) :
    (∀ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale →
      IsLocalHomeomorph (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) ∧
      ∀ p : A →ₐ[ℂ] ℂ, ∃ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), p ∈ e.source ∧
        (e : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) = coords g ∧
        ∀ a, AnalyticOnNhd ℂ (fun z => e.symm z a) e.target) ∧
    (Algebra.IsStandardSmoothOfRelativeDimension d ℂ A →
      (∃ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale) ∧
      ∃ h : HasAlgebraicCharts ℂ A d,
        letI := h.chartedSpace
        IsManifold 𝓘(ℂ, Fin d → ℂ) ω (A →ₐ[ℂ] ℂ) ∧
          ∀ a : A, ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω fun p : A →ₐ[ℂ] ℂ => p a) ∧
    (IsDomain A → ringKrullDim A = d →
      (∀ f : A, f ≠ 0 →
        IsClosed {p : A →ₐ[ℂ] ℂ | p f = 0} ∧ interior {p : A →ₐ[ℂ] ℂ | p f = 0} = ∅ ∧
        (∀ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A, g.Etale →
          volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0) ∧
        ∀ e : OpenPartialHomeomorph (A →ₐ[ℂ] ℂ) (Fin d → ℂ), IsAlgebraicChart e →
          volume (e '' (e.source ∩ {p | p f = 0})) = 0) ∧
      ∀ (ι : Type) [Countable ι] (E H M : ι → Type) [∀ i, NormedAddCommGroup (E i)]
        [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
        (I : ∀ i, ModelWithCorners ℂ (E i) (H i)) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]
        (φ : ∀ i, M i → (A →ₐ[ℂ] ℂ)), (∀ i, finrank ℂ (E i) < d) →
        (∀ i a, MDifferentiable (I i) 𝓘(ℂ) fun m => φ i m a) →
        ⋃ i, range (φ i) ≠ univ ∧ Dense (⋃ i, range (φ i))ᶜ) := by sorry
