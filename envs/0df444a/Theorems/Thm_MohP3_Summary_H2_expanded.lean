-- Prove2me | Theorems.Thm_MohP3_Summary_H2_expanded
-- name    : MohP3.Summary.H2_expanded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:42:16.033562+00:00
-- url     : https://prove2.me/theorems/52e3b85f-5905-570c-b19a-0a47f1292d23
-- title:
--   Summary: H2 expanded
-- statement:
--   The full expanded form of `H2`, as recorded in `witnesses.txt`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L88-L94
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L88-L94

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Definitions.Def_MohP3_HeightK
public import Definitions.Def_MohP3_HilbertBurch
public import Definitions.Def_MohP3
public import Theorems.Thm_MohP3_Gen_H2_expanded
public import Theorems.Thm_MohP3_H2_expanded

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary

theorem MohP3.Summary.H2_expanded : H2 =
    -80*x^6*y^2*z^3 + 170*x^5*y^4*z^2 + 80*x^4*y^6*z^6
    - 75*x^4*y^6*z + 15*x^4*y - 10*x^3*y^8*z^5
    + 32*x^3*y^3*z^4 - 25*x^2*y^10*z^4 - 98*x^2*y^5*z^3
    - 81*x^2*z^2 - 72*x*y^7*z^7 - 30*x*y^7*z^2
    + 102*x*y^2*z - 36*y^9*z^6 + 72*y^4*z^5 - 36*y^4 := by sorry
