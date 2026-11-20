-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_mul
-- name    : Nat.maxPrimeFac_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:52.311386+00:00
-- url     : https://prove2.me/theorems/44547bd8-e8bc-4c65-9254-0481ee87ad30
-- title:
--   Nat: max Prime Fac mul
-- statement:
--   The greatest prime factor of a product of nonzero natural numbers is the maximum of their
--   greatest prime factors.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L96-L106

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_mul (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by sorry
