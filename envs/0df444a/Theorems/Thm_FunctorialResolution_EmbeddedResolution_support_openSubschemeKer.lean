-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_openSubschemeKer
-- name    : FunctorialResolution.EmbeddedResolution.support_openSubschemeKer
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:48:54.947837+00:00
-- url     : https://prove2.me/theorems/e61b9327-186a-48c3-a093-c80579e2e89d
-- title:
--   Embedded Resolution: support open Subscheme Ker
-- statement:
--   The Embedded Resolution construction uses the support open Subscheme Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L24-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L24-L48

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
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

theorem FunctorialResolution.EmbeddedResolution.support_openSubschemeKer {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)
    (hW : IsClosed (W : Set Z.subscheme)) :
    ((openSubschemeKer Z W).support : Set X) = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by sorry
