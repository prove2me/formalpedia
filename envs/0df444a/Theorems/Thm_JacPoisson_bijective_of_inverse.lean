-- Prove2me | Theorems.Thm_JacPoisson_bijective_of_inverse
-- name    : JacPoisson.bijective_of_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:50:44.189709+00:00
-- url     : https://prove2.me/theorems/97d5108c-1793-4872-986a-6348224fb14b
-- title:
--   Jac Poisson: bijective of inverse
-- statement:
--   An algebra endomorphism whose images of the generators have a two-sided polynomial inverse
--   is bijective.
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L127-L141
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L127-L141

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {k : Type*} [CommRing k] {σ : Type*}

theorem JacPoisson.bijective_of_inverse (φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (G : RegularFunction k σ σ)
    (hGF : G.comp (fun v => φ (X v)) = RegularFunction.id k σ)
    (hFG : RegularFunction.comp (fun v => φ (X v)) G = RegularFunction.id k σ) :
    Function.Bijective φ := by sorry
