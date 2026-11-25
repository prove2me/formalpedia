-- Prove2me | Theorems.Thm_Hamiltonicity_ore
-- name    : Hamiltonicity.ore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:52.599815+00:00
-- url     : https://prove2.me/theorems/8c08ce72-5551-579a-81df-208169ec6f42
-- title:
--   Hamiltonicity: ore
-- statement:
--   **Ore's theorem (1960).** A graph on `n ≥ 3` vertices in which any two distinct non-adjacent
--   vertices have degree sum at least `n` is Hamiltonian.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L54-L86
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L54-L86

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_ClosureAux
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_MengerHamilton_Hamiltonian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.ore [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by sorry
