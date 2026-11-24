-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_eq_of_etale
-- name    : FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_eq_of_etale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:49.671419+00:00
-- url     : https://prove2.me/theorems/db7e646e-a7c0-4bea-8e93-84674c343b55
-- title:
--   Embedded Resolution: ring Krull Dim stalk eq of etale
-- statement:
--   The Embedded Resolution construction uses the ring Krull Dim stalk eq of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L121-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L121-L138

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

theorem FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_eq_of_etale {Y W : Scheme.{u}} (f : Y ⟶ W)
    [AlgebraicGeometry.Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    [_root_.IsRegularLocalRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (f.base y)) := by sorry
