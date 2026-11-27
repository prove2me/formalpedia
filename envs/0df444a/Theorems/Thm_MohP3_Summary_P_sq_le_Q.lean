-- Prove2me | Theorems.Thm_MohP3_Summary_P_sq_le_Q
-- name    : MohP3.Summary.P_sq_le_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:42:52.055185+00:00
-- url     : https://prove2.me/theorems/5f21c0bc-afd3-48f8-925a-18c21648f06c
-- title:
--   Summary: P sq le Q
-- statement:
--   The ten scaled identities of `identities.txt`; the scales are units in `ℚ`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L100-L100
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L100-L100

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
public import Theorems.Thm_MohP3_Gen_P_sq_le_Q
public import Theorems.Thm_MohP3_P_sq_le_Q

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary

theorem MohP3.Summary.P_sq_le_Q : P ^ 2 ≤ Q := by sorry
