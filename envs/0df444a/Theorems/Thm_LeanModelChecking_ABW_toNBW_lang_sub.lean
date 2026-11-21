-- Prove2me | Theorems.Thm_LeanModelChecking_ABW_toNBW_lang_sub
-- name    : LeanModelChecking.ABW.toNBW.lang_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:43:59.131224+00:00
-- url     : https://prove2.me/theorems/e3a9467b-8e00-455b-85ed-d15cb31e8275
-- title:
--   to NBW: lang sub
-- statement:
--   The to NBW construction uses the lang sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L45-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L45-L85

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking

theorem LeanModelChecking.ABW.toNBW.lang_sub {S Q} {A : ABW S Q} {w : Nat → S} :
    (ABW.toNBW A).language w → A.language w := by sorry
