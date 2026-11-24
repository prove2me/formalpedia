-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_affineSpaceIsSmooth
-- name    : FunctorialResolution.EmbeddedResolution.affineSpaceIsSmooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:29.333695+00:00
-- url     : https://prove2.me/theorems/880881dc-b6b4-4e35-a9b2-89b7de642455
-- title:
--   Embedded Resolution: affine Space Is Smooth
-- statement:
--   The Embedded Resolution construction uses the affine Space Is Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/AffineSpaceSmooth.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/AffineSpaceSmooth.lean#L32-L40

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
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

theorem FunctorialResolution.EmbeddedResolution.affineSpaceIsSmooth : AffineSpaceIsSmooth.{u} := by sorry
