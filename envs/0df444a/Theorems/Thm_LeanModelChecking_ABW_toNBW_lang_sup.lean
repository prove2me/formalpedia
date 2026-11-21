-- Prove2me | Theorems.Thm_LeanModelChecking_ABW_toNBW_lang_sup
-- name    : LeanModelChecking.ABW.toNBW.lang_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:03.718526+00:00
-- url     : https://prove2.me/theorems/80eb6d4d-fd64-414b-b4ba-a8be26ab92de
-- title:
--   to NBW: lang sup
-- statement:
--   The to NBW construction uses the lang sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L194-L321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L194-L321

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

theorem LeanModelChecking.ABW.toNBW.lang_sup {S Q} {A : ABW S Q} [Finite Q] {w : Nat → S} :
    A.language w → (ABW.toNBW A).language w := by sorry
