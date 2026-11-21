-- Prove2me | Theorems.Thm_LeanModelChecking_lemma1
-- name    : LeanModelChecking.lemma1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:08.287031+00:00
-- url     : https://prove2.me/theorems/79720006-4088-4229-8c03-1fc430421c2e
-- title:
--   Lean Model Checking: lemma1
-- statement:
--   The Lean Model Checking construction uses the lemma1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L87-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/ABWNBW.lean#L87-L89

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

theorem LeanModelChecking.lemma1 {α : Type} {a b c : Set α} {h : Disjoint a b} : a = (a ∪ (b ∩ c)) \ b := by sorry
