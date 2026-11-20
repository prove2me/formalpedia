-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_zero
-- name    : Nat.maxPrimeFac_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:19.795799+00:00
-- url     : https://prove2.me/theorems/b7a472e4-abdb-4e19-b193-f5d6022f69b9
-- title:
--   Nat: max Prime Fac zero
-- statement:
--   The Nat construction uses the max Prime Fac zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L41-L41

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_zero : maxPrimeFac 0 = 0 := by sorry
