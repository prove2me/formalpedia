-- Prove2me | Theorems.Thm_MellinDuality_pm_gi_pow_odd
-- name    : MellinDuality.pm_gi_pow_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:42:46.860128+00:00
-- url     : https://prove2.me/theorems/96328d92-8428-42ef-9490-53af1556eec3
-- title:
--   Mellin Duality: pm gi pow odd
-- statement:
--   Odd powers of `± i` are `± i`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L57-L63
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L57-L63

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality

theorem MellinDuality.pm_gi_pow_odd {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by sorry
