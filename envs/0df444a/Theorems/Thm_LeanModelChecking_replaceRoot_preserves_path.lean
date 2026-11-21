-- Prove2me | Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path
-- name    : LeanModelChecking.replaceRoot.preserves_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:15.408265+00:00
-- url     : https://prove2.me/theorems/a04ad5f2-d0d7-4a3c-af19-6846c75ba3dc
-- title:
--   replace Root: preserves path
-- statement:
--   The replace Root construction uses the preserves path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L297-L307
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L297-L307

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
open LeanModelChecking.replaceRoot
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
variable (r₁ : Iic φ₁) (r₂ : Iic φ₂) (G : DAG (Iic φ₁))

theorem LeanModelChecking.replaceRoot.preserves_path
  (p : ℕ → {q // q ≤ φ₂}) (p_path : (dag hle r₁ r₂ G).path p)
    : G.path (fun i => ⟨(p (i + 1)).val, path_after_1_prop hle r₁ r₂ G p p_path _ (by omega)⟩) := by sorry
