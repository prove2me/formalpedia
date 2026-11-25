-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_semigroupAlgebra_closure
-- name    : GroundTheory.Arith.Toric.semigroupAlgebra_closure
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:55:12.571726+00:00
-- url     : https://prove2.me/theorems/9238b3c3-ecf2-5811-9c2c-ea9b502e9726
-- title:
--   Toric: semigroup Algebra closure
-- statement:
--   The Toric construction uses the semigroup Algebra closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L58-L77

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
variable (k : Type*) [CommSemiring k] {G : Type*} [AddCommMonoid G]
variable {k}

theorem GroundTheory.Arith.Toric.semigroupAlgebra_closure (T : Set G) :
    semigroupAlgebra k (AddSubmonoid.closure T) =
      Algebra.adjoin k ((fun s => single s (1 : k)) '' T) := by sorry
