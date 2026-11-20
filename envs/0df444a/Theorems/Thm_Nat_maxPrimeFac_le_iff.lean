-- Prove2me | Theorems.Thm_Nat_maxPrimeFac_le_iff
-- name    : Nat.maxPrimeFac_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:48.138465+00:00
-- url     : https://prove2.me/theorems/e12be24d-89d0-4194-b052-81b22a73b7f2
-- title:
--   Nat: max Prime Fac le iff
-- statement:
--   The Nat construction uses the max Prime Fac le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean#L78-L80

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}

theorem Nat.maxPrimeFac_le_iff (hn : 1 < n) :
    n.maxPrimeFac ≤ m ↔ ∀ p, p.Prime → p ∣ n → p ≤ m := by sorry
