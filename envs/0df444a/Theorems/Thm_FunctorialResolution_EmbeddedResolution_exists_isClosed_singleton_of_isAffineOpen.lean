-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isClosed_singleton_of_isAffineOpen
-- name    : FunctorialResolution.EmbeddedResolution.exists_isClosed_singleton_of_isAffineOpen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:54.041488+00:00
-- url     : https://prove2.me/theorems/d3282e19-ce5a-49d4-aefd-f442ed4c946e
-- title:
--   Embedded Resolution: exists is Closed singleton of is Affine Open
-- statement:
--   The Embedded Resolution construction uses the exists is Closed singleton of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L152-L157

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

theorem FunctorialResolution.EmbeddedResolution.exists_isClosed_singleton_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ x : U.toScheme, IsClosed ({x} : Set U.toScheme) := by sorry
