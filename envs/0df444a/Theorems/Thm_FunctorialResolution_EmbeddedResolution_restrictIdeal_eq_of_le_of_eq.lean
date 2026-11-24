-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_of_le_of_eq
-- name    : FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_of_le_of_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:47.320493+00:00
-- url     : https://prove2.me/theorems/3fa132a6-4fe8-4424-b15d-4e31e61c8d75
-- title:
--   Embedded Resolution: restrict Ideal eq of le of eq
-- statement:
--   The Embedded Resolution construction uses the restrict Ideal eq of le of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L55-L59

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

theorem FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_of_le_of_eq {X : Scheme.{u}} {I J : X.IdealSheafData} {U V : X.Opens}
    (h : V ≤ U) (hU : restrictIdeal I U = restrictIdeal J U) :
    restrictIdeal I V = restrictIdeal J V := by sorry
