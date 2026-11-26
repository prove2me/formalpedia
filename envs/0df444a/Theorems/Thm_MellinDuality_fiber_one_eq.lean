-- Prove2me | Theorems.Thm_MellinDuality_fiber_one_eq
-- name    : MellinDuality.fiber_one_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:24.279363+00:00
-- url     : https://prove2.me/theorems/37a842c2-99ea-4731-a40f-21c1f4582a0a
-- title:
--   Mellin Duality: fiber one eq
-- statement:
--   `fiber χ 1` is the group `H` of nonzero fourth powers.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L272-L279
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L272-L279

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8

theorem MellinDuality.fiber_one_eq : fiber χ 1 = univ.filter fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x := by sorry
