-- Prove2me | Theorems.Thm_LeanModelChecking_release_mp_left
-- name    : LeanModelChecking.release_mp.left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:47.577056+00:00
-- url     : https://prove2.me/theorems/b793c304-17ab-4eb0-9898-f3eb2385fd0e
-- title:
--   release mp: left
-- statement:
--   The release mp construction uses the left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1414-L1424
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1414-L1424

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

theorem LeanModelChecking.release_mp.left (G_acc : G.accepting) {l} (H₁ : (⟨φ₁.release φ₂, le_refl _⟩, l) ∈
    G.V) (H₂ : (⟨φ₁.release φ₂, le_refl _⟩,
    l + 1) ∉ G.V) : φ₁.toABW.language (fun j => w (j + l)) := by sorry
