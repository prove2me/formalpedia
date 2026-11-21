-- Prove2me | Theorems.Thm_LeanModelChecking_and_mpr
-- name    : LeanModelChecking.and_mpr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:51.061693+00:00
-- url     : https://prove2.me/theorems/d7ba888d-72b2-4931-800e-5202db239e62
-- title:
--   Lean Model Checking: and mpr
-- statement:
--   The Lean Model Checking construction uses the and mpr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1207-L1236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1207-L1236

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

theorem LeanModelChecking.and_mpr {AP : Type} {φ₁ φ₂ : NNF AP} {w : ℕ
    → Letter AP} (H1 : φ₁.toABW.language w) (H2 : φ₂.toABW.language w)
    : (φ₁.and φ₂).toABW.language w := by sorry
