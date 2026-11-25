-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_smoothSubschemeIdealIsRadical
-- name    : FunctorialResolution.EmbeddedResolution.smoothSubschemeIdealIsRadical
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:21.7088+00:00
-- url     : https://prove2.me/theorems/7b598a1e-619f-48b4-b644-98a3c001da77
-- title:
--   Embedded Resolution: smooth Subscheme Ideal Is Radical
-- statement:
--   The Embedded Resolution construction uses the smooth Subscheme Ideal Is Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/RadicalCenterIdeal.lean#L20-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/RadicalCenterIdeal.lean#L20-L45

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationConstruction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_RadicalCenterIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.smoothSubschemeIdealIsRadical : SmoothSubschemeIdealIsRadical.{u} := by sorry
