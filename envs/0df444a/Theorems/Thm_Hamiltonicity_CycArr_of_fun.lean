-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_of_fun
-- name    : Hamiltonicity.CycArr.of_fun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:57.045927+00:00
-- url     : https://prove2.me/theorems/c2b522a1-27e2-5605-a7ec-74b8b188c297
-- title:
--   Cyc Arr: of fun
-- statement:
--   Build a cyclic arrangement from a function on `[0, m]` with `h m = h 0`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L80-L97
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L80-L97

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}

theorem Hamiltonicity.CycArr.of_fun {h : ℕ → V} (hm : 3 ≤ m) (hinj : ∀ i j, i < m → j < m → h i = h j → i = j)
    (hadj : ∀ i < m, G.Adj (h i) (h (i + 1))) (hend : h m = h 0) :
    CycArr G m (fun i => h (i % m)) := by sorry
