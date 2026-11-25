-- Prove2me | Theorems.Thm_Hamiltonicity_dirac
-- name    : Hamiltonicity.dirac
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:19:02.809643+00:00
-- url     : https://prove2.me/theorems/e79625d6-55a7-48b5-bc2f-0fb3871443e4
-- title:
--   Hamiltonicity: dirac
-- statement:
--   **Dirac's theorem (1952).** A graph on `n ≥ 3` vertices with minimum degree at least `n / 2`
--   is Hamiltonian.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L90-L96
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/Hamiltonian.lean#L90-L96

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

theorem Hamiltonicity.dirac [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian := by sorry
