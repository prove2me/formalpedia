-- Prove2me | Theorems.Thm_LeanModelChecking_release_mpr_base
-- name    : LeanModelChecking.release_mpr.base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:04.183954+00:00
-- url     : https://prove2.me/theorems/bd3d4f4c-66f3-406d-bc9c-16222a2f76df
-- title:
--   release mpr: base
-- statement:
--   The release mpr construction uses the base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1467-L1503
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1467-L1503

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
open LeanModelChecking.release_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
omit [DecidableEq S]

theorem LeanModelChecking.release_mpr.base
  (h1 : φ₁.toABW.language w)
  (h2 : φ₂.toABW.language w)
    : (φ₁.release φ₂).toABW.language w := by sorry
