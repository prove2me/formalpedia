-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_complComapSupport_eq
-- name    : FunctorialResolution.EmbeddedResolution.complComapSupport_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:09.936329+00:00
-- url     : https://prove2.me/theorems/3d7ee020-6a40-41e0-90ef-aaa20f0b5256
-- title:
--   Embedded Resolution: compl Comap Support eq
-- statement:
--   The Embedded Resolution construction uses the compl Comap Support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L15-L16

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.complComapSupport_eq {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    complComapSupport π Z = (Z.comap π).support.compl := by sorry
