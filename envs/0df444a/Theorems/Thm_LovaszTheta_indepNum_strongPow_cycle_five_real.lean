-- Prove2me | Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_real
-- name    : LovaszTheta.indepNum_strongPow_cycle_five_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:37:27.67765+00:00
-- url     : https://prove2.me/theorems/ab897437-ec35-5312-a6f1-1b59c6fe2329
-- title:
--   Lovasz Theta: indep Num strong Pow cycle five real
-- statement:
--   The Lovasz Theta construction uses the indep Num strong Pow cycle five real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L214-L222
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L214-L222

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.indepNum_strongPow_cycle_five_real (k : ℕ) :
    ((strongPow (cycleGraph 5) k).indepNum : ℝ) ≤ Real.sqrt 5 ^ k := by sorry
