-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_one
-- name    : Nat.maxPrimeFac_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:18.375966+00:00
-- url     : https://prove2.me/theorems/ccb74d89-dabb-4b14-ab39-2d1e9975a015
-- title:
--   Nat: max Prime Fac one
-- statement:
--   The Nat construction uses the max Prime Fac one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L42-L42
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L42-L42

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_one : maxPrimeFac 1 = 1 := by sorry
