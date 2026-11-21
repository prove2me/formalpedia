-- Prove2me | Theorems.Thm_LeanModelChecking_or_mpr_right
-- name    : LeanModelChecking.or_mpr.right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:33.02075+00:00
-- url     : https://prove2.me/theorems/046707e7-dba1-44a8-a8c2-148df1e77dd3
-- title:
--   or mpr: right
-- statement:
--   The or mpr construction uses the right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1267-L1278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1267-L1278

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

theorem LeanModelChecking.or_mpr.right : φ₂.toABW.language w → (φ₁.or φ₂).toABW.language w := by sorry
