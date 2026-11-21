-- Prove2me | Theorems.Thm_LeanModelChecking_exists_ABW_lang_for_LTL
-- name    : LeanModelChecking.exists_ABW_lang_for_LTL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:11.690854+00:00
-- url     : https://prove2.me/theorems/656f8794-641c-4706-8038-b880f514767b
-- title:
--   Lean Model Checking: exists ABW lang for LTL
-- statement:
--   The Lean Model Checking construction uses the exists ABW lang for LTL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1686-L1691
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1686-L1691

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking

theorem LeanModelChecking.exists_ABW_lang_for_LTL {AP} (f : LTL AP) :
    ∃ (Q : Type) (_ : Finite Q) (A : ABW (Letter AP) Q), f.language = A.language := by sorry
