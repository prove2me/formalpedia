-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_pow
-- name    : Nat.maxPrimeFac_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:33.936401+00:00
-- url     : https://prove2.me/theorems/635216ad-9898-4565-a98a-f53f6a189cd1
-- title:
--   Nat: max Prime Fac pow
-- statement:
--   The greatest prime factor of a power with nonzero exponent is the greatest prime factor of
--   its base.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L111-L123

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_pow : ∀ {k : ℕ}, k ≠ 0 → ∀ n, maxPrimeFac (n ^ k) = maxPrimeFac n := by sorry
