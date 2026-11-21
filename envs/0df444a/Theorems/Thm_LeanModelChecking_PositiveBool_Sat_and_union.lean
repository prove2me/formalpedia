-- Prove2me | Theorems.Thm_LeanModelChecking_PositiveBool_Sat_and_union
-- name    : LeanModelChecking.PositiveBool.Sat.and_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:36.780451+00:00
-- url     : https://prove2.me/theorems/e2d096a2-5604-49b5-8515-fce8ac9b17ca
-- title:
--   Sat: and union
-- statement:
--   The Sat construction uses the and union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L123-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L123-L129

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
open LeanModelChecking.PositiveBool

theorem LeanModelChecking.PositiveBool.Sat.and_union {Q} (f g : PositiveBool Q) {A B : Set Q} : PositiveBool.Sat A f
    → PositiveBool.Sat B g → PositiveBool.Sat (A ∪ B) (f.and g) := by sorry
