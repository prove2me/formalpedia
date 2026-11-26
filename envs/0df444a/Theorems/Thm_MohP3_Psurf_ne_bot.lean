-- Prove2me | Theorems.Thm_MohP3_Psurf_ne_bot
-- name    : MohP3.Psurf_ne_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:04:57.168151+00:00
-- url     : https://prove2.me/theorems/650949de-9aa1-533a-bd1e-75a111541af7
-- title:
--   Moh P3: Psurf ne bot
-- statement:
--   `y^5 - z^4` is a nonzero element of `Psurf`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L100-L111
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L100-L111

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

theorem MohP3.Psurf_ne_bot : Psurf ≠ ⊥ := by sorry
