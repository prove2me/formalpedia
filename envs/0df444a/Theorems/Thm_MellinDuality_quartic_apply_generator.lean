-- Prove2me | Theorems.Thm_MellinDuality_quartic_apply_generator
-- name    : MellinDuality.quartic_apply_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:42:46.493248+00:00
-- url     : https://prove2.me/theorems/e0dfc38f-b881-4916-aa15-cf3d441ff851
-- title:
--   Mellin Duality: quartic apply generator
-- statement:
--   On a generator, a quartic character takes the value `± i`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L128-L143
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L128-L143

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

theorem MellinDuality.quartic_apply_generator {g : (ZMod p)ˣ} (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    χ g = gi ∨ χ g = -gi := by sorry
