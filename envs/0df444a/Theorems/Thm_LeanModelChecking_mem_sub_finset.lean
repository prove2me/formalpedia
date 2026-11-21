-- Prove2me | Theorems.Thm_LeanModelChecking_mem_sub_finset
-- name    : LeanModelChecking.mem_sub_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:46.721201+00:00
-- url     : https://prove2.me/theorems/3b162219-0279-4d01-98fd-efea0baf963f
-- title:
--   Lean Model Checking: mem sub finset
-- statement:
--   The Lean Model Checking construction uses the mem sub finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1102-L1105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1102-L1105

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

theorem LeanModelChecking.mem_sub_finset {AP} [DecidableEq AP] {q f : NNF AP} : q ≤ f → q ∈ subFinset f := by sorry
