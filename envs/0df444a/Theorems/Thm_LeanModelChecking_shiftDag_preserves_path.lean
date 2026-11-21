-- Prove2me | Theorems.Thm_LeanModelChecking_shiftDag_preserves_path
-- name    : LeanModelChecking.shiftDag.preserves_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:13.874175+00:00
-- url     : https://prove2.me/theorems/7fc5b1df-8228-423d-a756-eff1f48be196
-- title:
--   shift Dag: preserves path
-- statement:
--   The shift Dag construction uses the preserves path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L412-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L412-L421

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
open LeanModelChecking.shiftDag
variable
  {T : Type} [PartialOrder T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
variable (r₁ : {q // q ≤ φ₁}) (r₂ : {q // q ≤ φ₂}) (G : DAG (Iic φ₁))

theorem LeanModelChecking.shiftDag.preserves_path
  (G : DAG (Iic φ₁)) (hrx : (r₁, 0) ∈ G.V)
  (p : ℕ → Iic φ₂) (p_path : (dag hle r₁ r₂ G hrx).path p)
    : G.path (fun i => ⟨(p (i + 1)).val,
        path_after_1_prop hle r₁ r₂ G hrx p p_path _ (by omega)⟩) := by sorry
