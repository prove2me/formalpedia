-- Prove2me | Theorems.Thm_LeanModelChecking_release_expand
-- name    : LeanModelChecking.release_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:18.718188+00:00
-- url     : https://prove2.me/theorems/41d913ad-b1ec-4c3f-af2c-64e0f1b9c91b
-- title:
--   Lean Model Checking: release expand
-- statement:
--   The Lean Model Checking construction uses the release expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L58-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L58-L85

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

theorem LeanModelChecking.release_expand {AP} (f g : NNF AP) :
    (f.release g).language = (g.and (f.or (f.release g).next)).language := by sorry
