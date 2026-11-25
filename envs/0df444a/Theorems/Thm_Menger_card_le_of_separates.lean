-- Prove2me | Theorems.Thm_Menger_card_le_of_separates
-- name    : Menger.card_le_of_separates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:56.242677+00:00
-- url     : https://prove2.me/theorems/e53a9db6-b9c4-5faf-bce2-1011bd7b901a
-- title:
--   Menger: card le of separates
-- statement:
--   **Weak duality.** Pairwise vertex-disjoint `A`–`B` paths are at most as many as the vertices
--   of any `A`–`B` separator.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L47-L59
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Menger.lean#L47-L59

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

theorem Menger.card_le_of_separates {G : SimpleGraph V} {A B X : Finset V}
    (hX : Separates G A B X) {m : ℕ} (a b : Fin m → V) (p : ∀ i, G.Walk (a i) (b i))
    (hA : ∀ i, a i ∈ A) (hB : ∀ i, b i ∈ B)
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support) :
    m ≤ X.card := by sorry
