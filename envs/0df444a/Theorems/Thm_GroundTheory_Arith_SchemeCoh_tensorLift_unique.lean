-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorLift_unique
-- name    : GroundTheory.Arith.SchemeCoh.tensorLift_unique
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:10.110567+00:00
-- url     : https://prove2.me/theorems/4299a59a-9b40-49de-834c-4567a0f4a03d
-- title:
--   Scheme Coh: tensor Lift unique
-- statement:
--   The Scheme Coh construction uses the tensor Lift unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L68-L72

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

theorem GroundTheory.Arith.SchemeCoh.tensorLift_unique {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) (f : M ⊗ N ⟶ G)
    (hf : tensorToSheaf M N ≫ (preMod X).map f = e) : f = tensorLift e := by sorry
