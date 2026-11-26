-- Prove2me | Theorems.Thm_MohP3_height_P_le_two
-- name    : MohP3.height_P_le_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:05:01.300892+00:00
-- url     : https://prove2.me/theorems/e6a53794-7be3-476a-96b6-b6199f616faa
-- title:
--   Moh P3: height P le two
-- statement:
--   Krull's height theorem: `P` is minimal over the two-generated ideal `Q`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L46-L53
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L46-L53

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

theorem MohP3.height_P_le_two : P.height ≤ 2 := by sorry
