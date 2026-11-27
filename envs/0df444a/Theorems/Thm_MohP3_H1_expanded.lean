-- Prove2me | Theorems.Thm_MohP3_H1_expanded
-- name    : MohP3.H1_expanded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:11.917709+00:00
-- url     : https://prove2.me/theorems/0ef76133-0556-4215-a8d4-0d2c9722a289
-- title:
--   Moh P3: H1 expanded
-- statement:
--   Expanded form of `H1`, as recorded in `witnesses.txt`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Certificate.lean#L26-L33
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Certificate.lean#L26-L33

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_H1_expanded

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.H1_expanded : H1 =
    128*x^7*y*z^3 - 272*x^6*y^3*z^2 - 128*x^5*y^5*z^6
    + 120*x^5*y^5*z - 24*x^5 + 16*x^4*y^7*z^5
    + 208*x^4*y^2*z^4 + 40*x^3*y^9*z^4 - 394*x^3*y^4*z^3
    - 144*x^2*y^6*z^7 + 291*x^2*y^6*z^2 + 177*x^2*y*z
    + 90*x*y^8*z^6 + 144*x*y^3*z^5 - 234*x*y^3
    + 81*y^10*z^5 - 162*y^5*z^4 + 81*z^3 := by sorry
