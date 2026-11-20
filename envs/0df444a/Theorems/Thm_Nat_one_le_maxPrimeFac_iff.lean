-- Prove2me | Theorems.Thm_Nat_one_le_maxPrimeFac_iff
-- name    : Nat.one_le_maxPrimeFac_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:22.672385+00:00
-- url     : https://prove2.me/theorems/304dc8d4-7025-4daa-a3d7-5c95da72083d
-- title:
--   Nat: one le max Prime Fac iff
-- statement:
--   The Nat construction uses the one le max Prime Fac iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L83-L86

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.one_le_maxPrimeFac_iff : ∀ {n : ℕ}, 1 ≤ maxPrimeFac n ↔ 1 ≤ n := by sorry
