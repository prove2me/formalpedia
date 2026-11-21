-- Prove2me | Theorems.Thm_LeanModelChecking_filterDag_preserves_path
-- name    : LeanModelChecking.filterDag.preserves_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:18.747109+00:00
-- url     : https://prove2.me/theorems/ecdd742b-d90b-455d-a04c-a756a93f8c44
-- title:
--   filter Dag: preserves path
-- statement:
--   The filter Dag construction uses the preserves path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L777-L783
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L777-L783

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
open LeanModelChecking.filterDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (leφ : φ ≤ Φ)
variable (G : DAG (Iic Φ)) (rΦ : Iic Φ) (rφ : Iic φ) (shift : ℕ)

theorem LeanModelChecking.filterDag.preserves_path {p : ℕ → Iic φ} (p_path : (dag leφ G rΦ rφ shift).path p) : G.path (fun i =>
    (p (i + 1)).embedLe leφ) := by sorry
