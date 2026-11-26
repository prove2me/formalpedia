-- Prove2me | Theorems.Thm_MellinDuality_quartic_values
-- name    : MellinDuality.quartic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:42:41.581471+00:00
-- url     : https://prove2.me/theorems/71f4bd1a-f078-5942-97f4-81fec68f1bd6
-- title:
--   Mellin Duality: quartic values
-- statement:
--   Nonzero values of a quartic character are fourth roots of unity.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L123-L125
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L123-L125

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

theorem MellinDuality.quartic_values {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi := by sorry
