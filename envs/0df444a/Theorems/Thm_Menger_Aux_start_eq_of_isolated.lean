-- Prove2me | Theorems.Thm_Menger_Aux_start_eq_of_isolated
-- name    : Menger.Aux.start_eq_of_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:27.326367+00:00
-- url     : https://prove2.me/theorems/b1ecd5eb-ca2f-4fd9-b36d-1fc9a590eac5
-- title:
--   Aux: start eq of isolated
-- statement:
--   A walk through an isolated vertex `v` starts at `v`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L409-L418
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L409-L418

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.start_eq_of_isolated {H : SimpleGraph V} {v : V} (hv : ∀ w, ¬ H.Adj v w) :
    ∀ {a b : V} (p : H.Walk a b), v ∈ p.support → a = v
  := by sorry
