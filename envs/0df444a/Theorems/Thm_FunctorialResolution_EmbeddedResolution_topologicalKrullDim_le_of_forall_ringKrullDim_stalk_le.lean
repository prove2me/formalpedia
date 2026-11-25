-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le
-- name    : FunctorialResolution.EmbeddedResolution.topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:29.594936+00:00
-- url     : https://prove2.me/theorems/cc056cc7-b626-4825-98a8-434f7889c7a9
-- title:
--   Embedded Resolution: topological Krull Dim le of forall ring Krull Dim stalk le
-- statement:
--   The Embedded Resolution construction uses the topological Krull Dim le of forall ring Krull Dim stalk le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L44-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L44-L100

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
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

theorem FunctorialResolution.EmbeddedResolution.topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) :
    topologicalKrullDim X ≤ d := by sorry
