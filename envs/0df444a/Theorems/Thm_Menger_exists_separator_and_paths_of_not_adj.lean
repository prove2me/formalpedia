-- Prove2me | Theorems.Thm_Menger_exists_separator_and_paths_of_not_adj
-- name    : Menger.exists_separator_and_paths_of_not_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:10:52.998038+00:00
-- url     : https://prove2.me/theorems/4f014896-a94d-4410-9c7b-356ce562d4dd
-- title:
--   Menger: exists separator and paths of not adj
-- statement:
--   **Menger's theorem, two-vertex form.** For distinct non-adjacent vertices `s`, `t` of a finite
--   graph there are a set `X` of vertices other than `s` and `t` meeting every `s`–`t` walk and `|X|`
--   paths from `s` to `t`, any two of which share only `s` and `t`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L83-L174
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L83-L174

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}

theorem Menger.exists_separator_and_paths_of_not_adj [Finite V] (G : SimpleGraph V)
    {s t : V} (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ X : Finset V, s ∉ X ∧ t ∉ X ∧ (∀ p : G.Walk s t, ∃ x ∈ X, x ∈ p.support) ∧
      ∃ p : Fin X.card → G.Walk s t, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∈ (p j).support → x = s ∨ x = t := by sorry
