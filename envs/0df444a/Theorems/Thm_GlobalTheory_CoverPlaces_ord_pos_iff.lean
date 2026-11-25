-- Prove2me | Theorems.Thm_GlobalTheory_CoverPlaces_ord_pos_iff
-- name    : GlobalTheory.CoverPlaces.ord_pos_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:29.043152+00:00
-- url     : https://prove2.me/theorems/c689e0df-1b3d-4acf-b074-41d3fbb9e81c
-- title:
--   Cover Places: ord pos iff
-- statement:
--   The Cover Places construction uses the ord pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEquivCoverPointsPlacesBaseChange.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEquivCoverPointsPlacesBaseChange.lean#L22-L31

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
import Theorems.Thm_GlobalTheory_ResDegPlace_ord_pos_iff

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

theorem GlobalTheory.CoverPlaces.ord_pos_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by sorry
