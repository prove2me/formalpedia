-- Prove2me | Theorems.Thm_MohP3_height_Ppoly_le_two
-- name    : MohP3.height_Ppoly_le_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:06:42.0027+00:00
-- url     : https://prove2.me/theorems/88ca6ead-b345-49af-95d1-5332fe81e746
-- title:
--   Moh P3: height Ppoly le two
-- statement:
--   The Moh P3 construction uses the height Ppoly le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L35-L47
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L35-L47

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

theorem MohP3.height_Ppoly_le_two : (Ppoly k).height ≤ 2 := by sorry
