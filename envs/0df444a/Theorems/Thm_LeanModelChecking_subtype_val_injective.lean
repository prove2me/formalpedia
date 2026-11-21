-- Prove2me | Theorems.Thm_LeanModelChecking_subtype_val_injective
-- name    : LeanModelChecking.subtype_val_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:27.107368+00:00
-- url     : https://prove2.me/theorems/a2fc00e1-0553-413f-b7d4-d03912caa0c1
-- title:
--   Lean Model Checking: subtype val injective
-- statement:
--   The Lean Model Checking construction uses the subtype val injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L40-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L40-L41

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

theorem LeanModelChecking.subtype_val_injective {α} {P : α → Prop} :
    @Function.Injective (Subtype P) α Subtype.val := by sorry
