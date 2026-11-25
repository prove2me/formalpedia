-- Prove2me | Theorems.Thm_Hamiltonicity_exists_trunc
-- name    : Hamiltonicity.exists_trunc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:49.572664+00:00
-- url     : https://prove2.me/theorems/255f0bcd-00bd-4445-9593-678699ee1c8c
-- title:
--   Hamiltonicity: exists trunc
-- statement:
--   Truncate a path ending in `B` at its first vertex in `B`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L41-L59
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L41-L59

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.exists_trunc {H : SimpleGraph V} (B : Set V) : ∀ {a b : V} (p : H.Walk a b), b ∈ B →
    p.IsPath → ∃ b' ∈ B, ∃ p' : H.Walk a b', p'.IsPath ∧ p'.support ⊆ p.support ∧
      ∀ y ∈ p'.support, y ∈ B → y = b'
  := by sorry
