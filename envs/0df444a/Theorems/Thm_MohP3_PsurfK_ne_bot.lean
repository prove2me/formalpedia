-- Prove2me | Theorems.Thm_MohP3_PsurfK_ne_bot
-- name    : MohP3.PsurfK_ne_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:07:16.369239+00:00
-- url     : https://prove2.me/theorems/1dfdd678-dc6c-4099-bc02-432bfe9e53ac
-- title:
--   Moh P3: Psurf K ne bot
-- statement:
--   `y^5 - z^4` is a nonzero element of `PsurfK`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L92-L103
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L92-L103

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
omit [CharZero k]

theorem MohP3.PsurfK_ne_bot : PsurfK k ≠ ⊥ := by sorry
