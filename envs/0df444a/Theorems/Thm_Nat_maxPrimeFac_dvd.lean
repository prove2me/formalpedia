-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_dvd
-- name    : Nat.maxPrimeFac_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:21.415506+00:00
-- url     : https://prove2.me/theorems/a0b95f58-fb1d-40c4-b229-7819f56ff207
-- title:
--   Nat: max Prime Fac dvd
-- statement:
--   The greatest prime factor of a natural number divides it.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L50-L56

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_dvd : ∀ {n : ℕ}, maxPrimeFac n ∣ n := by sorry
