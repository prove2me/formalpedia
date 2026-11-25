-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_ne_zero_isStandardSmoothOfRelativeDimension
-- name    : GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:26.188592+00:00
-- url     : https://prove2.me/theorems/98b6ee8f-d5fc-4556-92d9-10df8d99cb0c
-- title:
--   Affine Points: exists ne zero is Standard Smooth Of Relative Dimension
-- statement:
--   The Affine Points construction uses the exists ne zero is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L133-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L133-L144

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

theorem GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension [PerfectField K] [IsDomain A]
    [Algebra.FiniteType K A] (hd : ringKrullDim A = d) :
    ∃ s : A, s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by sorry
