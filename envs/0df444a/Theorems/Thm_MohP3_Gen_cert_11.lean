-- Prove2me | Theorems.Thm_MohP3_Gen_cert_11
-- name    : MohP3.Gen.cert_11
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:47:46.234115+00:00
-- url     : https://prove2.me/theorems/428b25ee-c410-500c-8945-2c35c349d033
-- title:
--   Gen: cert 11
-- statement:
--   Certificate identity for `f1 * f1` (scale `5832`).
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L132-L136
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L132-L136

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

theorem MohP3.Gen.cert_11 : (5832 : A) * (f1 x y z * f1 x y z) =
    (-1280*x^9*y^3*z^4 + 1600*x^8*y^5*z^3 - 500*x^7*y^7*z^2 + 512*x^6*y^4*z^5 + 800*x^5*y^6*z^4 - 1296*x^5*y*z^3 - 700*x^4*y^8*z^3 + 594*x^4*y^3*z^2 - 144*x^3*y^5*z^6 + 135*x^3*y^5*z - 243*x^3 - 558*x^2*y^7*z^5 + 1944*x*y^4*z^3 + 648*y^6*z^7) * H1 x y z
    + (-2048*x^10*y^2*z^4 + 2560*x^9*y^4*z^3 - 800*x^8*y^6*z^2 - 3328*x^7*y^3*z^5 + 6464*x^6*y^5*z^4 - 2740*x^5*y^7*z^3 - 3456*x^5*y^2*z^2 - 2304*x^4*y^4*z^6 + 2160*x^4*y^4*z + 4032*x^3*y^6*z^5 - 1296*x^3*y*z^4 - 2268*x^2*y^8*z^4 - 1134*x^2*y^3*z^3 - 1296*x*y^5*z^7 + 3159*x*y^5*z^2 - 243*x*z + 1458*y^7*z^6 - 1458*y^2) * H2 x y z := by sorry
