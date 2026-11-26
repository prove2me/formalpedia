-- Prove2me | Theorems.Thm_MohP3_height_Ppoly
-- name    : MohP3.height_Ppoly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:07:35.994035+00:00
-- url     : https://prove2.me/theorems/f9e6f8c1-5240-4564-8252-c496e17ad154
-- title:
--   Moh P3: height Ppoly
-- statement:
--   **The height of the curve ideal is two over any characteristic-zero
--   field.**
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L140-L141
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L140-L141

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

theorem MohP3.height_Ppoly : (Ppoly k).height = 2 := by sorry
