-- Prove2me | Theorems.Thm_MohP3_bot_lt_PsurfK
-- name    : MohP3.bot_lt_PsurfK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:07:24.686204+00:00
-- url     : https://prove2.me/theorems/e98eaf8d-67f3-476d-98be-c99410d86b89
-- title:
--   Moh P3: bot lt Psurf K
-- statement:
--   The Moh P3 construction uses the bot lt Psurf K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L122-L123
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L122-L123

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

theorem MohP3.bot_lt_PsurfK : (⊥ : Ideal (Rk k)) < PsurfK k := by sorry
