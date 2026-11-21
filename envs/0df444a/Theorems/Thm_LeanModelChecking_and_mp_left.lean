-- Prove2me | Theorems.Thm_LeanModelChecking_and_mp_left
-- name    : LeanModelChecking.and_mp.left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:35.418185+00:00
-- url     : https://prove2.me/theorems/d6484c92-7993-4a41-96d2-aac60d1c0b9e
-- title:
--   and mp: left
-- statement:
--   The and mp construction uses the left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1194-L1198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1194-L1198

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

theorem LeanModelChecking.and_mp.left {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.and φ₂).toABW.language w → φ₁.toABW.language w := by sorry
