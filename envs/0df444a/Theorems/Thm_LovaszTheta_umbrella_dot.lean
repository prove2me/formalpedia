-- Prove2me | Theorems.Thm_LovaszTheta_umbrella_dot
-- name    : LovaszTheta.umbrella_dot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:47:08.362741+00:00
-- url     : https://prove2.me/theorems/10653f0c-6966-441e-88e6-c586ed5af50b
-- title:
--   Lovasz Theta: umbrella dot
-- statement:
--   The Lovasz Theta construction uses the umbrella dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L198-L203
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L198-L203

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.umbrella_dot (i j : Fin 5) :
    dotProduct (umbrella i) (umbrella j) =
      umbS ^ 2 * Real.cos (pentAngle i - pentAngle j) + umbH ^ 2 := by sorry
