-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_schemeImageIdeal_eq_ker
-- name    : FunctorialResolution.Blowup.schemeImageIdeal_eq_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:00.647818+00:00
-- url     : https://prove2.me/theorems/9a903d4a-09bb-4315-b2a8-0cd028aa6a3a
-- title:
--   Blowup: scheme Image Ideal eq ker
-- statement:
--   The Blowup construction uses the scheme Image Ideal eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L44-L45

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

theorem FunctorialResolution.Blowup.schemeImageIdeal_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    schemeImageIdeal f I = (I.subschemeι ≫ f).ker := by sorry
