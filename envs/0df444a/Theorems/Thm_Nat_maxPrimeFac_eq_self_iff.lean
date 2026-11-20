-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
-- name    : Nat.maxPrimeFac_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:49.810725+00:00
-- url     : https://prove2.me/theorems/6c13502c-affc-457f-bd9f-36375236b0ea
-- title:
--   Nat: max Prime Fac eq self iff
-- statement:
--   The fixed points of `maxPrimeFac` are zero, one, and the primes.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L134-L143

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_eq_self_iff : maxPrimeFac n = n ↔ n ≤ 1 ∨ n.Prime := by sorry
