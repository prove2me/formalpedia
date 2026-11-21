-- Prove2me | Theorems.Thm_LeanModelChecking_not_exists_until_iff_forall
-- name    : LeanModelChecking.not_exists_until_iff_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:01.000781+00:00
-- url     : https://prove2.me/theorems/a201f21e-e23f-4711-bae1-ec991a94e8f5
-- title:
--   Lean Model Checking: not exists until iff forall
-- statement:
--   The Lean Model Checking construction uses the not exists until iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean#L55-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean#L55-L66

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking

theorem LeanModelChecking.not_exists_until_iff_forall {P Q : Nat → Prop} :
    (¬ ∃ i, Q i ∧ ∀ k < i, P k) ↔ ∀ i, ¬ Q i ∨ ∃ k < i, ¬ P k := by sorry
