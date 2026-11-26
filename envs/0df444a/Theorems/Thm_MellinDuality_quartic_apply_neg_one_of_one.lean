-- Prove2me | Theorems.Thm_MellinDuality_quartic_apply_neg_one_of_one
-- name    : MellinDuality.quartic_apply_neg_one_of_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:42.689045+00:00
-- url     : https://prove2.me/theorems/0715ab05-6fcb-4396-90a7-c25e92f687d0
-- title:
--   Mellin Duality: quartic apply neg one of one
-- statement:
--   **Proposition 1.1, order four, converse.** For `p ≡ 1 (mod 8)` a quartic character is even.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L177-L183
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L177-L183

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
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ

theorem MellinDuality.quartic_apply_neg_one_of_one (hp8 : p % 8 = 1) : χ (-1) = 1 := by sorry
