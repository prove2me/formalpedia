-- Prove2me | Theorems.Thm_MellinDuality_quadraticChar_eq_sq
-- name    : MellinDuality.quadraticChar_eq_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:06.32216+00:00
-- url     : https://prove2.me/theorems/88d9f304-da13-5905-9456-92ffa3d863b0
-- title:
--   Mellin Duality: quadratic Char eq sq
-- statement:
--   `(n/p) = χ(n)²` for `n ≠ 0`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L257-L263
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L257-L263

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

theorem MellinDuality.quadraticChar_eq_sq {n : ZMod p} (hn : n ≠ 0) :
    ((quadraticChar (ZMod p) n : ℤ) : GaussianInt) = χ n ^ 2 := by sorry
