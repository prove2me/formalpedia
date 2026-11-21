-- Prove2me | Theorems.Thm_LeanModelChecking_NNF_toABW_lang
-- name    : LeanModelChecking.NNF.toABW_lang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:06.558435+00:00
-- url     : https://prove2.me/theorems/75980020-2d8c-4e26-b3ff-a3684381b8a7
-- title:
--   NNF: to ABW lang
-- statement:
--   The NNF construction uses the to ABW lang property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1569-L1684
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1569-L1684

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

theorem LeanModelChecking.NNF.toABW_lang {AP} (ψ : NNF AP) : ψ.toABW.language = ψ.language := by sorry
