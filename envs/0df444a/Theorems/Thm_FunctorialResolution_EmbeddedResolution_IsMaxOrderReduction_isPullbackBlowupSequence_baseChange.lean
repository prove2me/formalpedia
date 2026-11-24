-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_isPullbackBlowupSequence_baseChange
-- name    : FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.isPullbackBlowupSequence_baseChange
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:13:21.831547+00:00
-- url     : https://prove2.me/theorems/4b97a790-bff5-4d15-b93c-6d63d44d652c
-- title:
--   Is Max Order Reduction: is Pullback Blowup Sequence base Change
-- statement:
--   The Is Max Order Reduction construction uses the is Pullback Blowup Sequence base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L393-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L393-L400

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

theorem FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.isPullbackBlowupSequence_baseChange {P : ℕ → Prop} {A B : PrincipalizationAssignment.{u}}
    (hs : IsMaxOrderReduction P A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
    (hV' : (T.baseChange L f).IsAdmissible) (hP' : P (T.baseChange L f).krullDimSucc) :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.baseChange L f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by sorry
