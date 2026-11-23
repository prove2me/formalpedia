-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_notMem_isStandardSmoothOfRelativeDimension
-- name    : GlobalTheory.AffinePoints.exists_notMem_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:15.833024+00:00
-- url     : https://prove2.me/theorems/01e8f086-77ca-49b8-84b8-425a68093592
-- title:
--   Affine Points: exists not Mem is Standard Smooth Of Relative Dimension
-- statement:
--   The Affine Points construction uses the exists not Mem is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L109-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L109-L131

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

theorem GlobalTheory.AffinePoints.exists_notMem_isStandardSmoothOfRelativeDimension [IsDomain A] [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) (P : Ideal A) [P.IsPrime] [Algebra.IsSmoothAt K P] :
    ∃ s ∉ P, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by sorry
