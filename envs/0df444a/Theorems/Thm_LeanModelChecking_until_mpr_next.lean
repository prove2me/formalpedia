-- Prove2me | Theorems.Thm_LeanModelChecking_until_mpr_next
-- name    : LeanModelChecking.until_mpr.next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:00.205183+00:00
-- url     : https://prove2.me/theorems/164e8090-67d9-4130-a23c-5e2a1f561b47
-- title:
--   until mpr: next
-- statement:
--   The until mpr construction uses the next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1372-L1403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1372-L1403

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

theorem LeanModelChecking.until_mpr.next
  {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
  (h1 : φ₁.toABW.language w)
  (h2 : (φ₁.until φ₂).toABW.language (fun j => w (j + 1)))
    : (φ₁.until φ₂).toABW.language w := by sorry
