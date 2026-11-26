-- Prove2me | Theorems.Thm_MellinDuality_sum_mul_two
-- name    : MellinDuality.sum_mul_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:35.078803+00:00
-- url     : https://prove2.me/theorems/096947dd-3e8c-4240-ba31-4333ad40171a
-- title:
--   Mellin Duality: sum mul two
-- statement:
--   Reindexing by `x = 2y`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L125-L128
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L125-L128

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.sum_mul_two (hp2 : p ≠ 2) {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ x, f x = ∑ y, f (2 * y) := by sorry
