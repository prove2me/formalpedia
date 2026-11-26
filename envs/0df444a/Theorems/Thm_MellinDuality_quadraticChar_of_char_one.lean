-- Prove2me | Theorems.Thm_MellinDuality_quadraticChar_of_char_one
-- name    : MellinDuality.quadraticChar_of_char_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:42.36588+00:00
-- url     : https://prove2.me/theorems/4991fc2e-346e-5629-90fc-a865b5bac85b
-- title:
--   Mellin Duality: quadratic Char of char one
-- statement:
--   The Mellin Duality construction uses the quadratic Char of char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L247-L249
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L247-L249

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
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem MellinDuality.quadraticChar_of_char_one {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 := by sorry
