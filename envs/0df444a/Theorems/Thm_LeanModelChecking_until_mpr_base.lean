-- Prove2me | Theorems.Thm_LeanModelChecking_until_mpr_base
-- name    : LeanModelChecking.until_mpr.base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:01.183564+00:00
-- url     : https://prove2.me/theorems/aa748b45-6d5d-41fb-8400-4d44459f23f6
-- title:
--   until mpr: base
-- statement:
--   The until mpr construction uses the base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1355-L1370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1355-L1370

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

theorem LeanModelChecking.until_mpr.base
  {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
  (h2 : φ₂.toABW.language w)
    : (φ₁.until φ₂).toABW.language w := by sorry
