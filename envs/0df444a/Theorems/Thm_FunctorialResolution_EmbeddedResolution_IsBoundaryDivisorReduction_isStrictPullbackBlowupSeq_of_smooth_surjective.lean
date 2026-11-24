-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsBoundaryDivisorReduction_isStrictPullbackBlowupSeq_of_smooth_surjective
-- name    : FunctorialResolution.EmbeddedResolution.IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:13:44.405592+00:00
-- url     : https://prove2.me/theorems/b490ff32-4fdd-43d2-9f8c-863bb6f6907b
-- title:
--   Is Boundary Divisor Reduction: is Strict Pullback Blowup Seq of smooth surjective
-- statement:
--   The Is Boundary Divisor Reduction construction uses the is Strict Pullback Blowup Seq of smooth surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L603-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L603-L615

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificateMonotone
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective {P : ℕ → Prop} {j : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hs : IsBoundaryDivisorReduction P j A B) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hP : P T.krullDimSucc) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc)
    (hO' : (T.pullbackAlong Y q h).IsOrderBoundedByMult)
    (hD' : (T.pullbackAlong Y q h).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    IsStrictPullbackBlowupSeq h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by sorry
