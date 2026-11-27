-- Prove2me | Theorems.Thm_MohP3_arithRank_P
-- name    : MohP3.arithRank_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:35.387873+00:00
-- url     : https://prove2.me/theorems/1a21c3f9-26ee-44d2-a921-88604b9e0a7b
-- title:
--   Moh P3: arith Rank P
-- statement:
--   **The arithmetic rank of `P` is two**: two equations suffice (the explicit
--   witnesses `H1, H2`), and by Krull's height theorem one equation cannot suffice.
--   Thus `P` is a set-theoretic complete intersection in the literal sense,
--   `arithRank P = height P = 2`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L154-L163
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L154-L163

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
open scoped Classical

theorem MohP3.arithRank_P : arithRank P = 2 := by sorry
