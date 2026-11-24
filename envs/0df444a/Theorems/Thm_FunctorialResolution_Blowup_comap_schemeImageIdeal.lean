-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_schemeImageIdeal
-- name    : FunctorialResolution.Blowup.comap_schemeImageIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:31.015208+00:00
-- url     : https://prove2.me/theorems/b83a87db-b017-422c-8b08-5ee4f61d00e2
-- title:
--   Blowup: comap scheme Image Ideal
-- statement:
--   The Blowup construction uses the comap scheme Image Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L79-L81

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
noncomputable section

theorem FunctorialResolution.Blowup.comap_schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : X.IdealSheafData) : (schemeImageIdeal f I).comap f = I := by sorry
