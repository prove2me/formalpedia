-- Prove2me | Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_two
-- name    : LovaszTheta.indepNum_strongPow_cycle_five_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:37:10.680217+00:00
-- url     : https://prove2.me/theorems/978608b0-c514-5416-8319-5fe8009802f0
-- title:
--   Lovasz Theta: indep Num strong Pow cycle five two
-- statement:
--   **Shannon (1956).** `α(C₅^⊠2) = 5`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L234-L258
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L234-L258

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.indepNum_strongPow_cycle_five_two : (strongPow (cycleGraph 5) 2).indepNum = 5 := by sorry
