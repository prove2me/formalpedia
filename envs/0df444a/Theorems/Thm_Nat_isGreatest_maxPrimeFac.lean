-- Prove2me | Theorems.Thm_Nat_isGreatest_maxPrimeFac
-- name    : Nat.isGreatest_maxPrimeFac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:37.627997+00:00
-- url     : https://prove2.me/theorems/4dcc3c22-b40a-48dc-ae3f-bfb3258d001b
-- title:
--   Nat: is Greatest max Prime Fac
-- statement:
--   The greatest prime factor of a natural number greater than one is the greatest of its prime
--   factors.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L67-L70

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.isGreatest_maxPrimeFac (hn : 1 < n) :
    IsGreatest {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) := by sorry
