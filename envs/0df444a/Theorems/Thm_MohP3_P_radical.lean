-- Prove2me | Theorems.Thm_MohP3_P_radical
-- name    : MohP3.P_radical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:57:09.43594+00:00
-- url     : https://prove2.me/theorems/399545f4-584a-5716-940a-ba2c062bb41f
-- title:
--   Moh P3: P radical
-- statement:
--   In particular `P` is a radical ideal.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Global.lean#L26-L26
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Global.lean#L26-L26

module
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.P_radical : P.radical = P := by sorry
