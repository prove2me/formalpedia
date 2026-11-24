-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_vanishesAlong_iff_le
-- name    : FunctorialResolution.EmbeddedResolution.vanishesAlong_iff_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:10.491207+00:00
-- url     : https://prove2.me/theorems/314c0c30-b850-440f-819d-01b6194c96b4
-- title:
--   Embedded Resolution: vanishes Along iff le
-- statement:
--   The Embedded Resolution construction uses the vanishes Along iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L76-L77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.vanishesAlong_iff_le {X : Scheme.{u}} (I J : X.IdealSheafData) :
    VanishesAlong I J ↔ I ≤ J := by sorry
