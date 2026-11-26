-- Prove2me | Theorems.Thm_MohP3_bot_lt_Psurf
-- name    : MohP3.bot_lt_Psurf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:05:34.573802+00:00
-- url     : https://prove2.me/theorems/ce15bce8-5cc7-51de-9d01-2cd8b00f9ca6
-- title:
--   Moh P3: bot lt Psurf
-- statement:
--   The Moh P3 construction uses the bot lt Psurf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L126-L127
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L126-L127

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

theorem MohP3.bot_lt_Psurf : (⊥ : Ideal R) < Psurf := by sorry
