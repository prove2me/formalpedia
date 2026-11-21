-- Prove2me | Theorems.Thm_LeanModelChecking_sub_finite
-- name    : LeanModelChecking.sub_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:51.626233+00:00
-- url     : https://prove2.me/theorems/dec585c2-dfcc-4071-85b4-2f4560d087ba
-- title:
--   Lean Model Checking: sub finite
-- statement:
--   The Lean Model Checking construction uses the sub finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1108-L1112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1108-L1112

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

theorem LeanModelChecking.sub_finite {AP} (f : NNF AP) : Finite { q // q ≤ f } := by sorry
