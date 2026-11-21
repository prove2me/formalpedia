-- Prove2me | Theorems.Thm_LeanModelChecking_release_mp_right
-- name    : LeanModelChecking.release_mp.right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:00.460174+00:00
-- url     : https://prove2.me/theorems/6e2192e4-1503-42fc-b3ed-8c69b3241fdb
-- title:
--   release mp: right
-- statement:
--   The release mp construction uses the right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1409-L1412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1409-L1412

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
open LeanModelChecking.release_mp
variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}

theorem LeanModelChecking.release_mp.right (G_acc : G.accepting) {l} (H : (⟨φ₁.release φ₂, le_refl _⟩,
    l) ∈ G.V) : φ₂.toABW.language (fun j => w (j + l)) := by sorry
