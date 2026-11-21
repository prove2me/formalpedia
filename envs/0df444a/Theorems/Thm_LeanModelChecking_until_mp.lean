-- Prove2me | Theorems.Thm_LeanModelChecking_until_mp
-- name    : LeanModelChecking.until_mp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:55.054675+00:00
-- url     : https://prove2.me/theorems/3f792ca4-1fb8-4f45-8203-3bfa5267eebd
-- title:
--   Lean Model Checking: until mp
-- statement:
--   The Lean Model Checking construction uses the until mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1311-L1353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1311-L1353

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

theorem LeanModelChecking.until_mp {S} {φ₁ φ₂ : NNF S} {w} (H : (φ₁.until φ₂).toABW.language w) : ∃ n,
    φ₂.toABW.language (fun j => w (j + n)) ∧ ∀ k < n, φ₁.toABW.language (fun j => w (j + k)) := by sorry
