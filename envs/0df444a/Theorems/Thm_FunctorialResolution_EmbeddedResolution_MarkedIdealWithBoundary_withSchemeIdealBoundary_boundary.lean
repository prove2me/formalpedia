-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_withSchemeIdealBoundary_boundary
-- name    : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.withSchemeIdealBoundary_boundary
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:53:56.612326+00:00
-- url     : https://prove2.me/theorems/a2e6f036-f954-5987-92b8-401886156871
-- title:
--   Marked Ideal With Boundary: with Scheme Ideal Boundary boundary
-- statement:
--   The Marked Ideal With Boundary construction uses the with Scheme Ideal Boundary boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean#L135-L137

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
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary

theorem FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.withSchemeIdealBoundary_boundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (J : Y.IdealSheafData)
    (E : List Y.IdealSheafData) : (T.withSchemeIdealBoundary Y q J E).boundary = E := by sorry
