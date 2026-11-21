-- Prove2me | Theorems.Thm_LeanModelChecking_antitone_nat_eventually_constant
-- name    : LeanModelChecking.antitone_nat_eventually_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:16.451662+00:00
-- url     : https://prove2.me/theorems/3fa260ef-4d2a-4c3a-b3f6-30e87c17c6af
-- title:
--   Lean Model Checking: antitone nat eventually constant
-- statement:
--   The Lean Model Checking construction uses the antitone nat eventually constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L43-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L43-L50

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

theorem LeanModelChecking.antitone_nat_eventually_constant
  {f : ℕ → ℕ} (hf : Antitone f)
    : ∃ N c, (∀ n ≥ N, f n = c) ∧ c ≤ f 0 := by sorry
