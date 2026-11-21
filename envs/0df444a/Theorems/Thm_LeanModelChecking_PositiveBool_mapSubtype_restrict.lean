-- Prove2me | Theorems.Thm_LeanModelChecking_PositiveBool_mapSubtype_restrict
-- name    : LeanModelChecking.PositiveBool.mapSubtype_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:36.814062+00:00
-- url     : https://prove2.me/theorems/131a8dd2-d148-4b26-9306-e75b0fd15f6b
-- title:
--   Positive Bool: map Subtype restrict
-- statement:
--   The Positive Bool construction uses the map Subtype restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L216-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L216-L220

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

theorem LeanModelChecking.PositiveBool.mapSubtype_restrict {T : Type} {α β : T → Prop} {ψ : PositiveBool T} {Y : Set (Subtype α)}
  (all_α : ψ.Forall α) (all_β : ψ.Forall β) (hle : ∀ {q}, β q → α q)
  (p_sat : PositiveBool.Sat Y (ψ.mapSubtype all_α))
    : PositiveBool.Sat {q | ⟨q.val, hle q.prop⟩ ∈ Y} (ψ.mapSubtype all_β) := by sorry
