-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow
-- name    : GroundTheory.Arith.Toric.LowerBound.pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:39.524802+00:00
-- url     : https://prove2.me/theorems/7a30a06c-f43f-4391-a92a-1d7e2d6acd17
-- title:
--   Lower Bound: pow
-- statement:
--   The Lower Bound construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L66-L74

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

theorem GroundTheory.Arith.Toric.LowerBound.pow {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a) (n : ℕ) :
    LowerBound φ (f ^ n) (n * a) := by sorry
