-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
-- name    : GroundTheory.Arith.Toric.LowerBound.mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:52.104744+00:00
-- url     : https://prove2.me/theorems/3a32232a-d9e4-4216-82d3-5a82f024c2db
-- title:
--   Lower Bound: mul
-- statement:
--   The Lower Bound construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L52-L58

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)
variable {φ}

theorem GroundTheory.Arith.Toric.LowerBound.mul {f g : AddMonoidAlgebra k G} {a b : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g b) : LowerBound φ (f * g) (a + b) := by sorry
