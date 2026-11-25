-- Prove2me | Theorems.Thm_LovaszTheta_pentAngle_sub
-- name    : LovaszTheta.pentAngle_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:46:54.280841+00:00
-- url     : https://prove2.me/theorems/326a66e9-e974-4397-9071-315d3d984884
-- title:
--   Lovasz Theta: pent Angle sub
-- statement:
--   Distinct non-adjacent pentagon vertices differ in angle by `±4π/5` or `±6π/5`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L152-L164
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L152-L164

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.pentAngle_sub (i j : Fin 5) (hij : i ≠ j) (hadj : ¬ (cycleGraph 5).Adj i j) :
    pentAngle i - pentAngle j = 4 * Real.pi / 5 ∨
    pentAngle i - pentAngle j = -(4 * Real.pi / 5) ∨
    pentAngle i - pentAngle j = 6 * Real.pi / 5 ∨
    pentAngle i - pentAngle j = -(6 * Real.pi / 5) := by sorry
