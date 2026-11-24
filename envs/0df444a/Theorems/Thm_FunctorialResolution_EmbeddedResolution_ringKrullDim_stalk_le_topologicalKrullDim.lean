-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_le_topologicalKrullDim
-- name    : FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_le_topologicalKrullDim
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:14.530406+00:00
-- url     : https://prove2.me/theorems/d5c9475c-4814-41e5-941d-15e62819d5e1
-- title:
--   Embedded Resolution: ring Krull Dim stalk le topological Krull Dim
-- statement:
--   The Embedded Resolution construction uses the ring Krull Dim stalk le topological Krull Dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L26-L35

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

theorem FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by sorry
