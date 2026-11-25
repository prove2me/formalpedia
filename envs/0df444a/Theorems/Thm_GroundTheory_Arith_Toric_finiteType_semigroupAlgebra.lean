-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_finiteType_semigroupAlgebra
-- name    : GroundTheory.Arith.Toric.finiteType_semigroupAlgebra
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:17.187816+00:00
-- url     : https://prove2.me/theorems/1d205289-065e-40a4-917f-d97cd149ed97
-- title:
--   Toric: finite Type semigroup Algebra
-- statement:
--   The Toric construction uses the finite Type semigroup Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean#L79-L84

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

theorem GroundTheory.Arith.Toric.finiteType_semigroupAlgebra {S : AddSubmonoid G} (hS : S.FG) :
    Algebra.FiniteType k (semigroupAlgebra k S) := by sorry
