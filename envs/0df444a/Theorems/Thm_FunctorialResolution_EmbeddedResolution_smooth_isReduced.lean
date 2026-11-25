-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_smooth_isReduced
-- name    : FunctorialResolution.EmbeddedResolution.smooth_isReduced
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:23.031802+00:00
-- url     : https://prove2.me/theorems/d82c8dc2-a433-4bee-bfb9-5bb5c555bab2
-- title:
--   Embedded Resolution: smooth is Reduced
-- statement:
--   The Embedded Resolution construction uses the smooth is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean#L266-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean#L266-L270

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
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

theorem FunctorialResolution.EmbeddedResolution.smooth_isReduced {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p) :
    IsReduced X := by sorry
