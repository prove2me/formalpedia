-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_strictTransform_eq_ker
-- name    : FunctorialResolution.Blowup.strictTransform_eq_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:40.237969+00:00
-- url     : https://prove2.me/theorems/3d0dede5-4300-4d96-84f8-b1e6a35e83d5
-- title:
--   Blowup: strict Transform eq ker
-- statement:
--   The Blowup construction uses the strict Transform eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L38-L39

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

theorem FunctorialResolution.Blowup.strictTransform_eq_ker {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransform f Z J = (strictTransformImmersion f Z J).ker := by sorry
