-- Prove2me | Theorems.Thm_Nat_isLUB_maxPrimeFac
-- name    : Nat.isLUB_maxPrimeFac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:47.679184+00:00
-- url     : https://prove2.me/theorems/57aa04b3-5734-4df4-b20f-576d5d2242c5
-- title:
--   Nat: is LUB max Prime Fac
-- statement:
--   The greatest prime factor of a natural number greater than one is the least upper bound of
--   its prime factors.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L74-L76

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.isLUB_maxPrimeFac (hn : 1 < n) :
    IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) := by sorry
