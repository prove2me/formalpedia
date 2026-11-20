-- Prove2me | Theorems.Thm_Nat_le_maxPrimeFac
-- name    : Nat.le_maxPrimeFac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:35.366642+00:00
-- url     : https://prove2.me/theorems/e4ce6358-d891-4e2c-a85c-55bd76e14ec0
-- title:
--   Nat: le max Prime Fac
-- statement:
--   Every prime factor of a nonzero natural number is at most its greatest prime factor.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L59-L63

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.le_maxPrimeFac (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by sorry
