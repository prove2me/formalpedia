-- Prove2me | Theorems.Thm_MohP3_Gen_cert_14
-- name    : MohP3.Gen.cert_14
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:08.148419+00:00
-- url     : https://prove2.me/theorems/c5b11570-8569-4158-b58d-b9c03f32e569
-- title:
--   Gen: cert 14
-- statement:
--   Certificate identity for `f1 * f4` (scale `8748`).
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L153-L157
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L153-L157

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

theorem MohP3.Gen.cert_14 : (8748 : A) * (f1 x y z * f4 x y z) =
    (640*x^7*y^4*z^5 - 800*x^6*y^6*z^4 + 250*x^5*y^8*z^3 - 480*x^5*y^3*z^2 - 576*x^4*y^5*z^6 + 300*x^4*y^5*z + 648*x^3*y^2*z^4 + 225*x^2*y^9*z^4 - 405*x^2*y^4*z^3 + 270*x*y^6*z^2 - 432*x*y*z + 324*y^8*z^6 - 324*y^3*z^5 + 324*y^3) * H1 x y z
    + (1024*x^8*y^3*z^5 - 1280*x^7*y^5*z^4 + 400*x^6*y^7*z^3 - 768*x^6*y^2*z^2 + 1152*x^5*y^4*z^6 + 480*x^5*y^4*z - 2592*x^4*y^6*z^5 + 1170*x^3*y^8*z^4 + 432*x^2*y^5*z^2 - 108*x^2*z - 648*x*y^7*z^6 + 648*x*y^2*z^5 - 648*x*y^2 + 729*y^9*z^5 - 729*y^4*z^4) * H2 x y z := by sorry
