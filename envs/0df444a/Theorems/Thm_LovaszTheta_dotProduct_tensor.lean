-- Prove2me | Theorems.Thm_LovaszTheta_dotProduct_tensor
-- name    : LovaszTheta.dotProduct_tensor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:46:50.589964+00:00
-- url     : https://prove2.me/theorems/08bf9d7e-60bb-49fd-96a7-b0125a497b7f
-- title:
--   Lovasz Theta: dot Product tensor
-- statement:
--   Dot products of tensor-product vectors factor coordinatewise.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L101-L108
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L101-L108

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.dotProduct_tensor {k : ℕ} {ι : Type*} [Fintype ι] (a b : Fin k → ι → ℝ) :
    dotProduct (fun j : Fin k → ι => ∏ i, a i (j i)) (fun j => ∏ i, b i (j i))
      = ∏ i, dotProduct (a i) (b i) := by sorry
