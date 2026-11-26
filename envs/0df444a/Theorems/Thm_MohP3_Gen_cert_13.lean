-- Prove2me | Theorems.Thm_MohP3_Gen_cert_13
-- name    : MohP3.Gen.cert_13
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:48:00.964066+00:00
-- url     : https://prove2.me/theorems/72c25725-bcc4-4e32-a1e2-a7b0523f70d2
-- title:
--   Gen: cert 13
-- statement:
--   Certificate identity for `f1 * f3` (scale `972`).
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L146-L150
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L146-L150

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

theorem MohP3.Gen.cert_13 : (972 : A) * (f1 x y z * f3 x y z) =
    (-80*x^6*y^2*z^2 + 50*x^5*y^4*z + 32*x^3*y^3*z^3 + 25*x^2*y^5*z^2 - 81*x^2*z + 54*x*y^2 + 36*y^4*z^4) * H1 x y z
    + (-128*x^7*y*z^2 + 80*x^6*y^3*z - 208*x^4*y^2*z^3 + 202*x^3*y^4*z^2 - 108*x^2*y - 72*x*y^3*z^4 + 81*y^5*z^3 - 81*z^2) * H2 x y z := by sorry
