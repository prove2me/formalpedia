-- Prove2me | Theorems.Thm_LeanModelChecking_alwaysDag_preserves_path
-- name    : LeanModelChecking.alwaysDag.preserves_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:23.153861+00:00
-- url     : https://prove2.me/theorems/39a69f19-fda7-4e3d-b647-18345490a974
-- title:
--   always Dag: preserves path
-- statement:
--   The always Dag construction uses the preserves path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L920-L971
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L920-L971

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
open LeanModelChecking.alwaysDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)
variable (G : ℕ → DAG (Iic φ))

theorem LeanModelChecking.alwaysDag.preserves_path
  (op : ℕ → Iic Φ) (op_path : (dag ltφ G).path op)
    : op = (fun _ => ⟨Φ, le_refl _⟩) ∨ (∃ i k,
        (Subtype.val <$> (G i)).path (fun i => (op (k + i)).val)) := by sorry
