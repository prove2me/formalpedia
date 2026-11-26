-- Prove2me | Theorems.Thm_MohP3_Gen_cert_44
-- name    : MohP3.Gen.cert_44
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:49.168146+00:00
-- url     : https://prove2.me/theorems/72554623-dc6f-5ff5-bec3-6e9b5ac8dd59
-- title:
--   Gen: cert 44
-- statement:
--   Certificate identity for `f4 * f4` (scale `13122`).
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L195-L199
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L195-L199

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

theorem MohP3.Gen.cert_44 : (13122 : A) * (f4 x y z * f4 x y z) =
    (-320*x^5*y^5*z^6 + 400*x^4*y^7*z^5 + 160*x^4*y^2*z^4 - 125*x^3*y^9*z^4 + 140*x^3*y^4*z^3 + 288*x^2*y^6*z^7 - 150*x^2*y^6*z^2 - 30*x^2*y*z - 180*x*y^8*z^6 - 288*x*y^3*z^5 - 180*x*y^3 + 162*z^3) * H1 x y z
    + (-512*x^6*y^4*z^6 + 640*x^5*y^6*z^5 + 256*x^5*y*z^4 - 200*x^4*y^8*z^4 + 224*x^4*y^3*z^3 - 576*x^3*y^5*z^7 - 240*x^3*y^5*z^2 - 48*x^3*z + 1008*x^2*y^7*z^6 + 576*x^2*y^2*z^5 - 288*x^2*y^2 - 405*x*y^9*z^5 - 648*x*y^4*z^4) * H2 x y z := by sorry
