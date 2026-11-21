-- Prove2me | Theorems.Thm_LeanModelChecking_or_mpr_left
-- name    : LeanModelChecking.or_mpr.left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:24.594621+00:00
-- url     : https://prove2.me/theorems/6c12e297-206d-46c0-8229-be13fe4d7a51
-- title:
--   or mpr: left
-- statement:
--   The or mpr construction uses the left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1253-L1264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1253-L1264

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
open LeanModelChecking.or_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
omit [DecidableEq S]

theorem LeanModelChecking.or_mpr.left : φ₁.toABW.language w → (φ₁.or φ₂).toABW.language w := by sorry
