-- Prove2me | Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five
-- name    : LovaszTheta.indepNum_strongPow_cycle_five
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:37:07.735563+00:00
-- url     : https://prove2.me/theorems/a6b96904-6d2c-53e4-a4b7-4df34bbb4faa
-- title:
--   Lovasz Theta: indep Num strong Pow cycle five
-- statement:
--   For the 5-cycle, `α(C₅^⊠k)² ≤ 5^k`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L225-L231
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L225-L231

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.indepNum_strongPow_cycle_five (k : ℕ) :
    (strongPow (cycleGraph 5) k).indepNum ^ 2 ≤ 5 ^ k := by sorry
