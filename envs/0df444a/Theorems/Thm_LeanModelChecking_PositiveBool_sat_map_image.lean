-- Prove2me | Theorems.Thm_LeanModelChecking_PositiveBool_sat_map_image
-- name    : LeanModelChecking.PositiveBool.sat_map_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:45:24.425099+00:00
-- url     : https://prove2.me/theorems/e22cf25c-077d-43f4-8ed2-0d7d1c53e7cf
-- title:
--   Positive Bool: sat map image
-- statement:
--   The Positive Bool construction uses the sat map image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L208-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean#L208-L214

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

theorem LeanModelChecking.PositiveBool.sat_map_image
  {T : Type} [PartialOrder T] {Q' Q : T} (hq : Q' ≤ Q)
  {ψ : PositiveBool T} {Y : Set { q // q ≤ Q' }}
  (H2 : Forall (fun x => x ≤ Q') ψ)
    : (ψ.mapSubtype H2).Sat Y
        ↔ (ψ.mapSubtype (H2.imp (by grind))).Sat (Subtype.embedLe hq '' Y) := by sorry
