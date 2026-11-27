-- Prove2me | Theorems.Thm_MohP3_two_le_height_Ppoly
-- name    : MohP3.two_le_height_Ppoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:07:34.35468+00:00
-- url     : https://prove2.me/theorems/30f56ea8-98d2-4fb6-a9f2-fe092e327170
-- title:
--   Moh P3: two le height Ppoly
-- statement:
--   The Moh P3 construction uses the two le height Ppoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L125-L136
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L125-L136

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

theorem MohP3.two_le_height_Ppoly : 2 ≤ (Ppoly k).height := by sorry
