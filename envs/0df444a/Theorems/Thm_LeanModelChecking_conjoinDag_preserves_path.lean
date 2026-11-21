-- Prove2me | Theorems.Thm_LeanModelChecking_conjoinDag_preserves_path
-- name    : LeanModelChecking.conjoinDag.preserves_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:15.460907+00:00
-- url     : https://prove2.me/theorems/ae1571a5-6feb-42ad-ab67-768090b22941
-- title:
--   conjoin Dag: preserves path
-- statement:
--   The conjoin Dag construction uses the preserves path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L541-L577
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L541-L577

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
open LeanModelChecking.conjoinDag
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ Φ : T}
  (leφ₁ : φ₁ ≤ Φ) (leφ₂ : φ₂ ≤ Φ)
variable
  (r₁ : Iic φ₁) (r₂ : Iic φ₂) (R : Iic Φ)
  (G₁ : DAG (Iic φ₁)) (G₂ : DAG (Iic φ₂))

theorem LeanModelChecking.conjoinDag.preserves_path
  (op : ℕ → Iic Φ) (op_path : (dag leφ₁ leφ₂ r₁ r₂ R G₁ G₂).path op)
  : (∃ k, (Subtype.val <$> G₁).path (fun i => (op (k + i)).val))
      ∨ (Subtype.val <$> G₂).path (fun i => (op (i + 1)).val) := by sorry
