-- Prove2me | Theorems.Thm_MellinDuality_isSquare_iff_char
-- name    : MellinDuality.isSquare_iff_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:11.955799+00:00
-- url     : https://prove2.me/theorems/9b6a5a7c-2b1a-43dd-adfe-2a996d38afe7
-- title:
--   Mellin Duality: is Square iff char
-- statement:
--   A nonzero `x` is a square exactly when `χ(x) = ± 1`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L223-L245
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L223-L245

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

theorem MellinDuality.isSquare_iff_char {x : ZMod p} (hx : x ≠ 0) : IsSquare x ↔ (χ x = 1 ∨ χ x = -1) := by sorry
