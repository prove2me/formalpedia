-- Prove2me | Theorems.Thm_MellinDuality_unit_apply_pow_four
-- name    : MellinDuality.unit_apply_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:03.701296+00:00
-- url     : https://prove2.me/theorems/c0152fbe-9823-5daf-b28c-d965c807ad11
-- title:
--   Mellin Duality: unit apply pow four
-- statement:
--   The Mellin Duality construction uses the unit apply pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L90-L92
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L90-L92

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

theorem MellinDuality.unit_apply_pow_four {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by sorry
