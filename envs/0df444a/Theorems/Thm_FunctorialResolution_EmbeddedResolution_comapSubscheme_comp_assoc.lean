-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comapSubscheme_comp_assoc
-- name    : FunctorialResolution.EmbeddedResolution.comapSubscheme_comp_assoc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:05.977944+00:00
-- url     : https://prove2.me/theorems/d52db0aa-60de-5f86-b082-c1a0671df650
-- title:
--   Embedded Resolution: comap Subscheme comp assoc
-- statement:
--   The Embedded Resolution construction uses the comap Subscheme comp assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/CertificateOpenRestriction.lean#L22-L25

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

theorem FunctorialResolution.EmbeddedResolution.comapSubscheme_comp_assoc {V W T : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData)
    (g : W ⟶ T) :
    comapSubscheme f D ≫ D.subschemeι ≫ g = (D.comap f).subschemeι ≫ f ≫ g := by sorry
