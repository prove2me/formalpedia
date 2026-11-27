-- Prove2me | Theorems.Thm_MohP3_arithRank_Ppoly
-- name    : MohP3.arithRank_Ppoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:22.052656+00:00
-- url     : https://prove2.me/theorems/9d125975-26dc-5a18-aa50-65b00a3b2e1c
-- title:
--   Moh P3: arith Rank Ppoly
-- statement:
--   **The arithmetic rank of the curve ideal is two over any
--   characteristic-zero field.**
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L146-L159
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L146-L159

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
open scoped Classical

theorem MohP3.arithRank_Ppoly : arithRank (Ppoly k) = 2 := by sorry
