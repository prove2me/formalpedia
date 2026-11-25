-- Prove2me | Theorems.Thm_MvPolynomial_RegularFunction_comp_aeval
-- name    : MvPolynomial.RegularFunction.comp_aeval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:40:51.440664+00:00
-- url     : https://prove2.me/theorems/2197b40b-02d0-5603-bfcd-76a1859a36a7
-- title:
--   Regular Function: comp aeval
-- statement:
--   `aeval` is compatible with composition of regular functions.
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Defs.lean#L73-L79
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Defs.lean#L73-L79

module
public import Mathlib
public import Definitions.Def_JacPoisson_Defs
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}
open MvPolynomial.RegularFunction

theorem MvPolynomial.RegularFunction.comp_aeval
    {σ τ ι : Type*}
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by sorry
