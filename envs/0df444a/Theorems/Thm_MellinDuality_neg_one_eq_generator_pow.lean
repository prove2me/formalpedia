-- Prove2me | Theorems.Thm_MellinDuality_neg_one_eq_generator_pow
-- name    : MellinDuality.neg_one_eq_generator_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:03.118239+00:00
-- url     : https://prove2.me/theorems/d4aab4cb-f19f-52f4-9bd7-e6f28e2fb07a
-- title:
--   Mellin Duality: neg one eq generator pow
-- statement:
--   `-1 = g ^ ((p - 1) / 2)` for a generator `g`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L147-L165
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L147-L165

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

theorem MellinDuality.neg_one_eq_generator_pow (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hgo : orderOf g = p - 1) :
    ((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) = -1 := by sorry
