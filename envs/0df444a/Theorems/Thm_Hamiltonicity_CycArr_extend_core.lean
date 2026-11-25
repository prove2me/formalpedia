-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_extend_core
-- name    : Hamiltonicity.CycArr.extend_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:58.625387+00:00
-- url     : https://prove2.me/theorems/83a4bd7f-f0b7-595c-95c6-64f99f80e9cf
-- title:
--   Cyc Arr: extend core
-- statement:
--   The detour construction with `a = 0` and `b = d`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/LongerCycle.lean#L31-L137
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/LongerCycle.lean#L31-L137

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

theorem Hamiltonicity.CycArr.extend_core (hC : CycArr G m f) {d : ℕ} (hd1 : 1 ≤ d) (hdm : d < m)
    (Q : G.Walk (f 0) (f d)) (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f 0 ∨ y = f d)
    (hadj : G.Adj (f 1) (f (d + 1))) :
    ∃ g, CycArr G (m + Q.length - 1) g := by sorry
