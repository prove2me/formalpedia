-- Prove2me | Theorems.Thm_MellinDuality_gi_pow_eq_one_iff
-- name    : MellinDuality.gi_pow_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:49.602648+00:00
-- url     : https://prove2.me/theorems/ec611b29-9f47-4221-b3b3-070c7d2392d4
-- title:
--   Mellin Duality: gi pow eq one iff
-- statement:
--   The Mellin Duality construction uses the gi pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L266-L273
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L266-L273

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
omit hp hχ

theorem MellinDuality.gi_pow_eq_one_iff {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ j = 1 ↔ 4 ∣ j := by sorry
