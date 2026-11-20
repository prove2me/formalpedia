-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_le
-- name    : Nat.maxPrimeFac_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:49.111876+00:00
-- url     : https://prove2.me/theorems/b5c21dbb-ebc4-41eb-8aea-8426d2eb3ae8
-- title:
--   Nat: max Prime Fac le
-- statement:
--   The greatest prime factor of a natural number is at most that number.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L146-L149

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_le : ∀ {n : ℕ}, maxPrimeFac n ≤ n := by sorry
