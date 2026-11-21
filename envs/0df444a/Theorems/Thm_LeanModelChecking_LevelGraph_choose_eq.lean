-- Prove2me | Theorems.Thm_LeanModelChecking_LevelGraph_choose_eq
-- name    : LeanModelChecking.LevelGraph.choose_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:01.751676+00:00
-- url     : https://prove2.me/theorems/cab68dd0-9cb3-4425-83b1-693ae47c7292
-- title:
--   Level Graph: choose eq
-- statement:
--   The Level Graph construction uses the choose eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L156-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L156-L157

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
open LeanModelChecking.LevelGraph

theorem LeanModelChecking.LevelGraph.choose_eq {α} {p : α → Prop} (P : ∃ a, p a) {a} (eq : P.choose = a) : p a := by sorry
