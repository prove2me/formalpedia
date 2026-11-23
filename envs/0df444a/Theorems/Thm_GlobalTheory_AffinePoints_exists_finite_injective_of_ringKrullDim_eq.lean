-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_finite_injective_of_ringKrullDim_eq
-- name    : GlobalTheory.AffinePoints.exists_finite_injective_of_ringKrullDim_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:31.908402+00:00
-- url     : https://prove2.me/theorems/13dc5298-ccad-4fc6-8916-b45dcd36f9fc
-- title:
--   Affine Points: exists finite injective of ring Krull Dim eq
-- statement:
--   The Affine Points construction uses the exists finite injective of ring Krull Dim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L69-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L69-L85

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
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

theorem GlobalTheory.AffinePoints.exists_finite_injective_of_ringKrullDim_eq [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) :
    ∃ g : MvPolynomial (Fin d) K →ₐ[K] A, Function.Injective g ∧ g.Finite := by sorry
