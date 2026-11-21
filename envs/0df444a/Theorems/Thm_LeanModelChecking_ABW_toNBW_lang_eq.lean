-- Prove2me | Theorems.Thm_LeanModelChecking_ABW_toNBW_lang_eq
-- name    : LeanModelChecking.ABW.toNBW.lang_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:02.21128+00:00
-- url     : https://prove2.me/theorems/d6133102-295f-4670-8308-89b156015cce
-- title:
--   to NBW: lang eq
-- statement:
--   The to NBW construction uses the lang eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L323-L325
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L323-L325

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

theorem LeanModelChecking.ABW.toNBW.lang_eq {S Q} (A : ABW S Q) [Finite Q] : A.language = (ABW.toNBW A).language := by sorry
