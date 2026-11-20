-- Prove2me | Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
-- name    : Nat.Prime.maxPrimeFac_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:38.541235+00:00
-- url     : https://prove2.me/theorems/bfd7021d-4c71-4f94-96ff-819944f2620c
-- title:
--   Prime: max Prime Fac eq self
-- statement:
--   The greatest prime factor of a prime is the prime itself.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L127-L130

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.Prime.maxPrimeFac_eq_self (hp : p.Prime) : maxPrimeFac p = p := by sorry
