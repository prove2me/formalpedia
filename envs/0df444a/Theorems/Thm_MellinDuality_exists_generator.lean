-- Prove2me | Theorems.Thm_MellinDuality_exists_generator
-- name    : MellinDuality.exists_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:42:43.978807+00:00
-- url     : https://prove2.me/theorems/7452dbdb-058a-501c-8031-6064713ec334
-- title:
--   Mellin Duality: exists generator
-- statement:
--   A generator of `(ZMod p)ˣ`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L83-L88
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L83-L88

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

theorem MellinDuality.exists_generator :
    ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧ ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by sorry
