-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_strictTransformOpens_eq
-- name    : FunctorialResolution.Blowup.strictTransformOpens_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:58.92691+00:00
-- url     : https://prove2.me/theorems/6394f8fb-ccb0-4868-a7ce-6c8df543db69
-- title:
--   Blowup: strict Transform Opens eq
-- statement:
--   The Blowup construction uses the strict Transform Opens eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L22-L24

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

theorem FunctorialResolution.Blowup.strictTransformOpens_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformOpens f Z J =
      (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl := by sorry
