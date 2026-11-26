-- Prove2me | Theorems.Thm_MellinDuality_char_eq_one_iff
-- name    : MellinDuality.char_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:54.086503+00:00
-- url     : https://prove2.me/theorems/66596975-cbfb-46c1-8dff-a95e23b603a6
-- title:
--   Mellin Duality: char eq one iff
-- statement:
--   `χ(n) = 1` exactly when `n` is a nonzero fourth power.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L276-L291
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L276-L291

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

theorem MellinDuality.char_eq_one_iff {n : ZMod p} (hn : n ≠ 0) : χ n = 1 ↔ ∃ y : ZMod p, y ^ 4 = n := by sorry
