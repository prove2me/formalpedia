-- Prove2me | Theorems.Thm_MellinDuality_quartic_apply_two
-- name    : MellinDuality.quartic_apply_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:44.30273+00:00
-- url     : https://prove2.me/theorems/12692967-eebe-5080-bd6c-f6d881f80a5a
-- title:
--   Mellin Duality: quartic apply two
-- statement:
--   For `p ≡ 5 (mod 8)`, `χ 2 = ± i`: `2` is a quadratic non-residue.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L207-L211
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L207-L211

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

theorem MellinDuality.quartic_apply_two (hp8 : p % 8 = 5) : χ 2 = gi ∨ χ 2 = -gi := by sorry
