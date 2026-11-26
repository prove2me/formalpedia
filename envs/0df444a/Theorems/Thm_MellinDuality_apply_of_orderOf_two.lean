-- Prove2me | Theorems.Thm_MellinDuality_apply_of_orderOf_two
-- name    : MellinDuality.apply_of_orderOf_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:32.949794+00:00
-- url     : https://prove2.me/theorems/3599d22f-ce63-59c4-996b-40be90d862d6
-- title:
--   Mellin Duality: apply of order Of two
-- statement:
--   **Proposition 1.1, order two.** A character of order two is real: its values are
--   `0` and `± 1`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L107-L115
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L107-L115

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

theorem MellinDuality.apply_of_orderOf_two (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 2)
    (a : ZMod p) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by sorry
