-- Prove2me | Theorems.Thm_Nat_prime_maxPrimeFac_of_one_lt
-- name    : Nat.prime_maxPrimeFac_of_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:26.276599+00:00
-- url     : https://prove2.me/theorems/00eae817-62c8-4f74-8efe-b7e26885d5d9
-- title:
--   Nat: prime max Prime Fac of one lt
-- statement:
--   The Nat construction uses the prime max Prime Fac of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L44-L47

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.prime_maxPrimeFac_of_one_lt (h : 1 < n) : n.maxPrimeFac.Prime := by sorry
