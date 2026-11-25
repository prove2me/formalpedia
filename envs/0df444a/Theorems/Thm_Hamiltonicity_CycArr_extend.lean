-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_extend
-- name    : Hamiltonicity.CycArr.extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:06.127835+00:00
-- url     : https://prove2.me/theorems/ad2e4c8e-bba6-5753-a206-aafe9f8d006a
-- title:
--   Cyc Arr: extend
-- statement:
--   **Lengthening a cycle.** A path `Q` of length at least two between distinct vertices `f a`,
--   `f b` of a cycle, with interior off the cycle, together with an edge between the successors
--   `f (a + 1)` and `f (b + 1)`, gives a cycle of length `m + |Q| - 1`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/LongerCycle.lean#L142-L176
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/LongerCycle.lean#L142-L176

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_LongerCycle
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}

theorem Hamiltonicity.CycArr.extend (hC : CycArr G m f) {a b : ℕ} (hab : f a ≠ f b) (Q : G.Walk (f a) (f b))
    (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f a ∨ y = f b)
    (hadj : G.Adj (f (a + 1)) (f (b + 1))) :
    ∃ g, CycArr G (m + Q.length - 1) g := by sorry
