-- Prove2me | Theorems.Thm_MellinDuality_apply_neg_one_of_odd_orderOf
-- name    : MellinDuality.apply_neg_one_of_odd_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:32.859169+00:00
-- url     : https://prove2.me/theorems/e09cb5c7-1620-5a22-a2f7-52a153ebe18b
-- title:
--   Mellin Duality: apply neg one of odd order Of
-- statement:
--   **Proposition 1.1, odd orders.** A character of odd order is even.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L95-L103
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L95-L103

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.apply_neg_one_of_odd_orderOf {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (h : Odd (orderOf χ)) : χ (-1) = 1 := by sorry
