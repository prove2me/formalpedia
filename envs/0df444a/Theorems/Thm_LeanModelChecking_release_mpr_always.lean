-- Prove2me | Theorems.Thm_LeanModelChecking_release_mpr_always
-- name    : LeanModelChecking.release_mpr.always
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:46:30.043909+00:00
-- url     : https://prove2.me/theorems/cb3ab425-46ae-4966-84b3-dfac5eac5954
-- title:
--   release mpr: always
-- statement:
--   The release mpr construction uses the always property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1433-L1463
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L1433-L1463

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

theorem LeanModelChecking.release_mpr.always
  (hg : ∀ i, φ₂.toABW.language (fun j => w (j + i)))
    : (φ₁.release φ₂).toABW.language w := by sorry
