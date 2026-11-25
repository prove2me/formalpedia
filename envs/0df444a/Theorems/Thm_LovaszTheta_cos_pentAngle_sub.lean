-- Prove2me | Theorems.Thm_LovaszTheta_cos_pentAngle_sub
-- name    : LovaszTheta.cos_pentAngle_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:47:07.109139+00:00
-- url     : https://prove2.me/theorems/591837d0-2fe3-4c23-8552-0d9d6c32a0c8
-- title:
--   Lovasz Theta: cos pent Angle sub
-- statement:
--   The cosine of the angle between distinct non-adjacent pentagon vertices.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L167-L175
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L167-L175

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.cos_pentAngle_sub (i j : Fin 5) (hij : i ≠ j) (hadj : ¬ (cycleGraph 5).Adj i j) :
    Real.cos (pentAngle i - pentAngle j) = -(1 + √5) / 4 := by sorry
