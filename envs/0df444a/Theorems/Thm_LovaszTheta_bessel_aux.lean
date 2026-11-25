-- Prove2me | Theorems.Thm_LovaszTheta_bessel_aux
-- name    : LovaszTheta.bessel_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:37:49.767798+00:00
-- url     : https://prove2.me/theorems/fadb6b42-20d2-49fb-8714-9e24f63b3c63
-- title:
--   Lovasz Theta: bessel aux
-- statement:
--   Bessel's inequality for a finite orthonormal family.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L50-L78
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L50-L78

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.bessel_aux {ι κ : Type*} [Fintype ι] (S : Finset κ) (u : κ → ι → ℝ)
    (hu1 : ∀ i ∈ S, dotProduct (u i) (u i) = 1)
    (hu0 : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dotProduct (u i) (u j) = 0) (c : ι → ℝ) :
    ∑ i ∈ S, dotProduct c (u i) ^ 2 ≤ dotProduct c c := by sorry
