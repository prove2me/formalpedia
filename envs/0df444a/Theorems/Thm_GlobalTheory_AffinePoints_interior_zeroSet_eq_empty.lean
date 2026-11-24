-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_interior_zeroSet_eq_empty
-- name    : GlobalTheory.AffinePoints.interior_zeroSet_eq_empty
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:55:25.494097+00:00
-- url     : https://prove2.me/theorems/e7410675-be07-468f-bb3f-c8abb7aa201c
-- title:
--   Affine Points: interior zero Set eq empty
-- statement:
--   The Affine Points construction uses the interior zero Set eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNeZeroIsStandardSmoothOfRelativeDimension.lean#L201-L203

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

theorem GlobalTheory.AffinePoints.interior_zeroSet_eq_empty [IsDomain A] [Algebra.FiniteType ℂ A] {f : A} (hf : f ≠ 0) :
    interior {p : A →ₐ[ℂ] ℂ | p f = 0} = ∅ := by sorry
