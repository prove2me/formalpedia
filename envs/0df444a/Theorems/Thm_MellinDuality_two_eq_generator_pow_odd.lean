-- Prove2me | Theorems.Thm_MellinDuality_two_eq_generator_pow_odd
-- name    : MellinDuality.two_eq_generator_pow_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:12.223268+00:00
-- url     : https://prove2.me/theorems/86e8feb3-3371-4c81-b110-38542fa7f9ec
-- title:
--   Mellin Duality: two eq generator pow odd
-- statement:
--   `2` is an odd power of any generator when `p ≡ 5 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L187-L204
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L187-L204

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
omit hχ

theorem MellinDuality.two_eq_generator_pow_odd (hp8 : p % 8 = 5) {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    ∃ e : ℕ, Odd e ∧ ((g ^ e : (ZMod p)ˣ) : ZMod p) = 2 := by sorry
