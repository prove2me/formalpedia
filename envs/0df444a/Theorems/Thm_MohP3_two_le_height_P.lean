-- Prove2me | Theorems.Thm_MohP3_two_le_height_P
-- name    : MohP3.two_le_height_P
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:05:41.857014+00:00
-- url     : https://prove2.me/theorems/3dcf88ca-33b5-57c8-8386-23e0a97e3ed3
-- title:
--   Moh P3: two le height P
-- statement:
--   The Moh P3 construction uses the two le height P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L131-L142
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L131-L142

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

theorem MohP3.two_le_height_P : 2 ≤ P.height := by sorry
