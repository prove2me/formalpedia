-- Prove2me | Theorems.Thm_Menger_Aux_path_R
-- name    : Menger.Aux.path_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:07:57.950325+00:00
-- url     : https://prove2.me/theorems/d19f6762-dd4e-5738-a1b6-d001b97a78f9
-- title:
--   Aux: path R
-- statement:
--   The vertices other than the end of a path from `A` meeting `X ⊇ Y` only at its end are
--   reachable from `A` avoiding `Y`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L67-L75
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L67-L75

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.path_R {H : SimpleGraph V} {A X Y : Finset V} (hYX : Y ⊆ X) {a v : V} (ha : a ∈ A)
    (p : H.Walk a v) (hp : p.IsPath) (hX : ∀ w ∈ p.support, w ∈ X → w = v) {w : V}
    (hw : w ∈ p.support) (hne : w ≠ v) : R H A Y w := by sorry
