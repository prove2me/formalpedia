-- Prove2me | Theorems.Thm_MohP3_Summary_arithRank_P
-- name    : MohP3.Summary.arithRank_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:43:07.054932+00:00
-- url     : https://prove2.me/theorems/a6f746c0-ab09-5cbb-9e82-59ad72b4d626
-- title:
--   Summary: arith Rank P
-- statement:
--   The arithmetic rank of the Moh curve ideal is two: it is a set-theoretic
--   complete intersection in the literal sense.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L116-L116
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L116-L116

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
public import Theorems.Thm_MohP3_arithRank_P

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary

theorem MohP3.Summary.arithRank_P : arithRank P = 2 := by sorry
