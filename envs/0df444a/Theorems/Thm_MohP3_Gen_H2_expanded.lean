-- Prove2me | Theorems.Thm_MohP3_Gen_H2_expanded
-- name    : MohP3.Gen.H2_expanded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:28.365791+00:00
-- url     : https://prove2.me/theorems/298bdf82-7f89-5526-b64c-f0c68efbc05c
-- title:
--   Gen: H2 expanded
-- statement:
--   Expanded form of `H2`, as recorded in `witnesses.txt`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L101-L108
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L101-L108

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)

theorem MohP3.Gen.H2_expanded : H2 x y z =
    -80*x^6*y^2*z^3 + 170*x^5*y^4*z^2 + 80*x^4*y^6*z^6
    - 75*x^4*y^6*z + 15*x^4*y - 10*x^3*y^8*z^5
    + 32*x^3*y^3*z^4 - 25*x^2*y^10*z^4 - 98*x^2*y^5*z^3
    - 81*x^2*z^2 - 72*x*y^7*z^7 - 30*x*y^7*z^2
    + 102*x*y^2*z - 36*y^9*z^6 + 72*y^4*z^5 - 36*y^4 := by sorry
