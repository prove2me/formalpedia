-- Prove2me | Theorems.Thm_LeanModelChecking_next_mpr
-- name    : LeanModelChecking.next_mpr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:56.354034+00:00
-- url     : https://prove2.me/theorems/63809b7b-733a-4caa-8239-e15f8d8858bd
-- title:
--   Lean Model Checking: next mpr
-- statement:
--   The Lean Model Checking construction uses the next mpr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1296-L1309
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1296-L1309

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

theorem LeanModelChecking.next_mpr {AP : Type} {φ : NNF AP} {w} : (φ.toABW.language fun j =>
    w (j + 1)) → φ.next.toABW.language w := by sorry
