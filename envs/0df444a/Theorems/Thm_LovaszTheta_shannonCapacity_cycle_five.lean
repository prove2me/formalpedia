-- Prove2me | Theorems.Thm_LovaszTheta_shannonCapacity_cycle_five
-- name    : LovaszTheta.shannonCapacity_cycle_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:37:41.831861+00:00
-- url     : https://prove2.me/theorems/c3ccadce-0ef3-4b57-81f5-853b8cfd845e
-- title:
--   Lovasz Theta: shannon Capacity cycle five
-- statement:
--   **Lovász (1979).** The Shannon capacity of the pentagon is `√5`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L265-L284
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L265-L284

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.shannonCapacity_cycle_five : shannonCapacity (cycleGraph 5) = Real.sqrt 5 := by sorry
