-- Prove2me | Theorems.Thm_LeanModelChecking_DAG_path_mapped
-- name    : LeanModelChecking.DAG.path_mapped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:28.810489+00:00
-- url     : https://prove2.me/theorems/4ffd1e52-453d-464c-8363-f1f2c98c1694
-- title:
--   DAG: path mapped
-- statement:
--   The DAG construction uses the path mapped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L239-L251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L239-L251

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
open LeanModelChecking.DAG

theorem LeanModelChecking.DAG.path_mapped {α β} [Nonempty α] (G : DAG α) (f : α → β) (f_inj : Function.Injective f) (p : ℕ
    → β) (p_path : (f <$> G).path p) : G.path ((Function.invFun f) ∘ p) := by sorry
