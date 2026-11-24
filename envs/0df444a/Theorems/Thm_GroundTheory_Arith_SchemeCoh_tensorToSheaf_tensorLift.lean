-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorToSheaf_tensorLift
-- name    : GroundTheory.Arith.SchemeCoh.tensorToSheaf_tensorLift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:51.186288+00:00
-- url     : https://prove2.me/theorems/938a57f8-d343-4c72-8705-7df1d333409c
-- title:
--   Scheme Coh: tensor To Sheaf tensor Lift
-- statement:
--   The Scheme Coh construction uses the tensor To Sheaf tensor Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L62-L66

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

theorem GroundTheory.Arith.SchemeCoh.tensorToSheaf_tensorLift {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) :
    tensorToSheaf M N ≫ (preMod X).map (tensorLift e) = e := by sorry
