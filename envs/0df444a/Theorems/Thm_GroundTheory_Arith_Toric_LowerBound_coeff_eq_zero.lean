-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_coeff_eq_zero
-- name    : GroundTheory.Arith.Toric.LowerBound.coeff_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:39.159935+00:00
-- url     : https://prove2.me/theorems/7fc20ae7-20dd-4224-ac33-aae9be40cabf
-- title:
--   Lower Bound: coeff eq zero
-- statement:
--   The Lower Bound construction uses the coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean#L76-L79

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

theorem GroundTheory.Arith.Toric.LowerBound.coeff_eq_zero {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    {m : G} (hm : φ m < a) : f.coeff m = 0 := by sorry
