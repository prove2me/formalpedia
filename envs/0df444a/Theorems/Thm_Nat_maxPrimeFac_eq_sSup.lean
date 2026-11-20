-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_eq_sSup
-- name    : Nat.maxPrimeFac_eq_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:57.171877+00:00
-- url     : https://prove2.me/theorems/fea7a09a-2d67-431a-a366-d9e9001dfe27
-- title:
--   Nat: max Prime Fac eq s Sup
-- statement:
--   Away from `n = 1`, the computable greatest prime factor agrees with its supremum
--   characterization.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L153-L157

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_eq_sSup (hn_one : n ≠ 1) :
    maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by sorry
