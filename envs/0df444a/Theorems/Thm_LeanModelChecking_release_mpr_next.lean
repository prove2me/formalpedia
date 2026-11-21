-- Prove2me | Theorems.Thm_LeanModelChecking_release_mpr_next
-- name    : LeanModelChecking.release_mpr.next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:06.593754+00:00
-- url     : https://prove2.me/theorems/e516f559-2e52-475d-bc0b-5823baa5be9e
-- title:
--   release mpr: next
-- statement:
--   The release mpr construction uses the next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1507-L1538
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1507-L1538

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

theorem LeanModelChecking.release_mpr.next
  (h2 : φ₂.toABW.language w)
  (h3 : (φ₁.release φ₂).toABW.language (fun j => w (j + 1)))
    : (φ₁.release φ₂).toABW.language w := by sorry
