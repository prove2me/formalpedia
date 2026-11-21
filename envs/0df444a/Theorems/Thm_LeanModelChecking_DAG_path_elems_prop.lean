-- Prove2me | Theorems.Thm_LeanModelChecking_DAG_path_elems_prop
-- name    : LeanModelChecking.DAG.path_elems_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:37.389174+00:00
-- url     : https://prove2.me/theorems/33cd3859-8b9b-4342-ba00-7b2f942d5a38
-- title:
--   DAG: path elems prop
-- statement:
--   The DAG construction uses the path elems prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L253-L256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L253-L256

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

theorem LeanModelChecking.DAG.path_elems_prop {α} {P : α → Prop} {G : DAG (Subtype P)} {p : ℕ
    → α} (p_path : (Subtype.val <$> G).path p) : ∀ i, P (p i) := by sorry
