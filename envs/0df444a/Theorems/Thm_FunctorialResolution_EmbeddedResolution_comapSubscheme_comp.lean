-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comapSubscheme_comp
-- name    : FunctorialResolution.EmbeddedResolution.comapSubscheme_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:45.924798+00:00
-- url     : https://prove2.me/theorems/232e5cda-0874-4025-89ed-1413b4061e08
-- title:
--   Embedded Resolution: comap Subscheme comp
-- statement:
--   The Embedded Resolution construction uses the comap Subscheme comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean#L18-L20

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_CertificateOpenRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.comapSubscheme_comp {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    comapSubscheme f D ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by sorry
