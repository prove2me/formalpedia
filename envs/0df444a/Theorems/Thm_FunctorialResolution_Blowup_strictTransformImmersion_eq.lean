-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_strictTransformImmersion_eq
-- name    : FunctorialResolution.Blowup.strictTransformImmersion_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:50.029749+00:00
-- url     : https://prove2.me/theorems/f5abd375-0c94-43d8-ab7e-2e1148f5d644
-- title:
--   Blowup: strict Transform Immersion eq
-- statement:
--   The Blowup construction uses the strict Transform Immersion eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L30-L32

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

theorem FunctorialResolution.Blowup.strictTransformImmersion_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformImmersion f Z J =
      (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι := by sorry
