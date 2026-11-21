-- Prove2me | Theorems.Thm_LeanModelChecking_LTL_exists_equiv_nnf
-- name    : LeanModelChecking.LTL.exists_equiv_nnf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:44:04.853254+00:00
-- url     : https://prove2.me/theorems/a4b7d6cb-fdeb-479e-9156-e1b0e12105cf
-- title:
--   LTL: exists equiv nnf
-- statement:
--   The LTL construction uses the exists equiv nnf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean#L131-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean#L131-L134

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

theorem LeanModelChecking.LTL.exists_equiv_nnf {AP} (ψ : LTL AP) :
    ∃ (nnf : NNF AP), ψ.language = nnf.language := by sorry
