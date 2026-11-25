-- Prove2me | Theorems.Thm_GlobalTheory_CoverPlaces_surjective_of_detect
-- name    : GlobalTheory.CoverPlaces.surjective_of_detect
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:39.773606+00:00
-- url     : https://prove2.me/theorems/4aa2cdab-cb06-4e58-9987-f7c51c65b7ff
-- title:
--   Cover Places: surjective of detect
-- statement:
--   The Cover Places construction uses the surjective of detect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEquivCoverPointsPlacesBaseChange.lean#L33-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEquivCoverPointsPlacesBaseChange.lean#L33-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEquivCoverPointsPlacesBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.CoverPlaces
variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

theorem GlobalTheory.CoverPlaces.surjective_of_detect [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {T : Type} [Finite T]
    (Z : T → Pts O A) (hZ : ∀ x, (∀ t, 0 ≤ ord ϖ (Z t) x) → x ∈ As O A) :
    Function.Surjective Z := by sorry
