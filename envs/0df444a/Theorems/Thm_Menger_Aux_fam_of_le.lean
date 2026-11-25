-- Prove2me | Theorems.Thm_Menger_Aux_fam_of_le
-- name    : Menger.Aux.fam_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:09:02.802898+00:00
-- url     : https://prove2.me/theorems/81d03b01-43dd-527d-88c9-b8caebf840e0
-- title:
--   Aux: fam of le
-- statement:
--   Core of Menger's theorem: if every `A`–`B` separator has at least `k` vertices, there are
--   `k` disjoint `A`–`B` paths.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L386-L406
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L386-L406

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.fam_of_le [Finite V] (n : ℕ) : ∀ (G : SimpleGraph V), G.edgeSet.ncard = n →
    ∀ (A B : Finset V) (k : ℕ), (∀ X, Sep G A B X → k ≤ X.card) → Fam G A B k := by sorry
