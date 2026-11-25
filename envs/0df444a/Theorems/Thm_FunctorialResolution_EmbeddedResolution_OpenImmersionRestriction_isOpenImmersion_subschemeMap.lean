-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isOpenImmersion_subschemeMap
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.isOpenImmersion_subschemeMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:03.376235+00:00
-- url     : https://prove2.me/theorems/1386fc36-4cdd-487d-bf9d-4a6a26cb0456
-- title:
--   Open Immersion Restriction: is Open Immersion subscheme Map
-- statement:
--   The Open Immersion Restriction construction uses the is Open Immersion subscheme Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/OpenRestriction.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/OpenRestriction.lean#L27-L37

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_OpenRestriction
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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.isOpenImmersion_subschemeMap {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
    (D : W.IdealSheafData) (g : (D.comap f).subscheme ⟶ D.subscheme)
    (hg : g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f) :
    IsOpenImmersion g := by sorry
