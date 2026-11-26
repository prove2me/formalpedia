-- Prove2me | Theorems.Thm_MellinDuality_quartic_apply_neg_one
-- name    : MellinDuality.quartic_apply_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:12.794212+00:00
-- url     : https://prove2.me/theorems/f9f36070-f410-4d39-ab70-5a9a6d7faa2c
-- title:
--   Mellin Duality: quartic apply neg one
-- statement:
--   **Proposition 1.1, order four.** For `p ≡ 5 (mod 8)` a quartic character is odd.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L168-L174
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L168-L174

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

theorem MellinDuality.quartic_apply_neg_one (hp8 : p % 8 = 5) : χ (-1) = -1 := by sorry
