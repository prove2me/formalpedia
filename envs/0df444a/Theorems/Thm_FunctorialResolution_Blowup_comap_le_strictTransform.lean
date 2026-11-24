-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_le_strictTransform
-- name    : FunctorialResolution.Blowup.comap_le_strictTransform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:10.266438+00:00
-- url     : https://prove2.me/theorems/395bc08f-df07-43dc-a40f-f43dc4fd8328
-- title:
--   Blowup: comap le strict Transform
-- statement:
--   The Blowup construction uses the comap le strict Transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L83-L87

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

theorem FunctorialResolution.Blowup.comap_le_strictTransform {X X₁ : Scheme.{u}} (p : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    D.comap p ≤ strictTransform p Z D := by sorry
