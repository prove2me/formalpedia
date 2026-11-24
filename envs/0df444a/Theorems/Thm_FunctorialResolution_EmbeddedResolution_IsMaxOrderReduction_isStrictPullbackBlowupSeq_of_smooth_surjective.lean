-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_isStrictPullbackBlowupSeq_of_smooth_surjective
-- name    : FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:14:41.406484+00:00
-- url     : https://prove2.me/theorems/f49712fd-5047-421e-92fd-60967cbdc6b4
-- title:
--   Is Max Order Reduction: is Strict Pullback Blowup Seq of smooth surjective
-- statement:
--   The Is Max Order Reduction construction uses the is Strict Pullback Blowup Seq of smooth surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L384-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L384-L391

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

theorem FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective {P : ℕ → Prop} {A B : PrincipalizationAssignment.{u}}
    (hs : IsMaxOrderReduction P A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc) :
    IsStrictPullbackBlowupSeq h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by sorry
