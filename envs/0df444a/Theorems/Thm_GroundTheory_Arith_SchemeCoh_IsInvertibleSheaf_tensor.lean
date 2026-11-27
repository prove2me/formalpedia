-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsInvertibleSheaf_tensor
-- name    : GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.tensor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:05.362271+00:00
-- url     : https://prove2.me/theorems/83c48ab4-a32c-5a7f-8751-e6e9a0d0d667
-- title:
--   Is Invertible Sheaf: tensor
-- statement:
--   The Is Invertible Sheaf construction uses the tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L277-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L277-L283

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.tensor {M N : X.Modules} (hM : IsInvertibleSheaf M)
    (hN : IsInvertibleSheaf N) : IsInvertibleSheaf (M ⊗ N) := by sorry
