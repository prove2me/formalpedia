-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_nilIsStrictNormalCrossingsOnAffineSpace
-- name    : FunctorialResolution.EmbeddedResolution.nilIsStrictNormalCrossingsOnAffineSpace
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:12.071505+00:00
-- url     : https://prove2.me/theorems/9ce6b04e-6b02-424e-9fd4-7f140517d0e3
-- title:
--   Embedded Resolution: nil Is Strict Normal Crossings On Affine Space
-- statement:
--   The Embedded Resolution construction uses the nil Is Strict Normal Crossings On Affine Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/AffineSpaceSmooth.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/AffineSpaceSmooth.lean#L42-L47

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

theorem FunctorialResolution.EmbeddedResolution.nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace.{u} := by sorry
