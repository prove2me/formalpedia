-- Prove2me | Theorems.Thm_LeanModelChecking_until_expand_repeat
-- name    : LeanModelChecking.until_expand_repeat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:39.58128+00:00
-- url     : https://prove2.me/theorems/b08cfb7a-bc30-4d85-9aa3-154fbccdd0f7
-- title:
--   Lean Model Checking: until expand repeat
-- statement:
--   The Lean Model Checking construction uses the until expand repeat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L87-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L87-L119

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

theorem LeanModelChecking.until_expand_repeat {AP} (f g : NNF AP) : ∀ w, (f.until g).language w
    ↔ ∃ n, (NNF.repeatAndNext f g n).language w := by sorry
