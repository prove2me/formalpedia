-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIso_restrict_lastStructMap_of_centersLieOver
-- name    : FunctorialResolution.EmbeddedResolution.isIso_restrict_lastStructMap_of_centersLieOver
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:00.243002+00:00
-- url     : https://prove2.me/theorems/1c9b4624-557b-4607-b170-90c2e35db11e
-- title:
--   Embedded Resolution: is Iso restrict last Struct Map of centers Lie Over
-- statement:
--   The Embedded Resolution construction uses the is Iso restrict last Struct Map of centers Lie Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/IsoAwayFromCenters.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/IsoAwayFromCenters.lean#L62-L66

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_IsoAwayFromCenters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isIso_restrict_lastStructMap_of_centersLieOver {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S) :
    IsIso (s.lastStructMap ∣_ U) := by sorry
