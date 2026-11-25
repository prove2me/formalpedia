-- Prove2me | Theorems.Thm_Hamiltonicity_exists_path_avoiding
-- name    : Hamiltonicity.exists_path_avoiding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:26.846955+00:00
-- url     : https://prove2.me/theorems/b691dcc2-e62f-45bd-862e-bf4ce590e32b
-- title:
--   Hamiltonicity: exists path avoiding
-- statement:
--   If `G - S` is connected, two vertices outside `S` are joined by a path avoiding `S`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L62-L71
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L62-L71

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.exists_path_avoiding {G : SimpleGraph V} (S : Set V) (hS : (G.induce Sᶜ).Connected)
    {a b : V} (ha : a ∉ S) (hb : b ∉ S) :
    ∃ p : G.Walk a b, p.IsPath ∧ ∀ y ∈ p.support, y ∉ S := by sorry
