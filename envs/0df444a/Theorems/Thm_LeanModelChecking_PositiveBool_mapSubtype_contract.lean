-- Prove2me | Theorems.Thm_LeanModelChecking_PositiveBool_mapSubtype_contract
-- name    : LeanModelChecking.PositiveBool.mapSubtype_contract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:41.279027+00:00
-- url     : https://prove2.me/theorems/ae722148-a5ec-45a0-a751-0234600da820
-- title:
--   Positive Bool: map Subtype contract
-- statement:
--   The Positive Bool construction uses the map Subtype contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L183-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L183-L190

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

theorem LeanModelChecking.PositiveBool.mapSubtype_contract
  {α} {P Q : α → Prop}
  {φ : PositiveBool α}
  {Y : Set (Subtype P)} {fq : φ.Forall Q} {fp : φ.Forall P}
  (hsat : (φ.mapSubtype fp).Sat Y) (f : Subtype P → Subtype Q)
  (hf : ∀ (x : Subtype P), Q (x.val) → (f x).val = x)
    : (φ.mapSubtype fq).Sat (f '' Y) := by sorry
