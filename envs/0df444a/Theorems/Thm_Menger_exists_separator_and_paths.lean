-- Prove2me | Theorems.Thm_Menger_exists_separator_and_paths
-- name    : Menger.exists_separator_and_paths
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:09:51.741421+00:00
-- url     : https://prove2.me/theorems/7c45ff25-e9e4-4106-8dd8-a7ba6e30e4f4
-- title:
--   Menger: exists separator and paths
-- statement:
--   **Menger's theorem (1927), set form.** In a finite graph there are an `A`–`B` separator `X`
--   and `|X|` pairwise vertex-disjoint paths from `A` to `B`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L63-L78
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L63-L78

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

theorem Menger.exists_separator_and_paths [Finite V] (G : SimpleGraph V)
    (A B : Finset V) :
    ∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support := by sorry
