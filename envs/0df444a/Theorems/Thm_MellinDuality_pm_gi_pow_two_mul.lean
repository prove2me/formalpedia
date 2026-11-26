-- Prove2me | Theorems.Thm_MellinDuality_pm_gi_pow_two_mul
-- name    : MellinDuality.pm_gi_pow_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:42:45.14345+00:00
-- url     : https://prove2.me/theorems/ffcb2f3a-672d-5d23-8147-0f8378b76520
-- title:
--   Mellin Duality: pm gi pow two mul
-- statement:
--   Even powers of `± i` are `(-1) ^ j`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L66-L69
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L66-L69

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality

theorem MellinDuality.pm_gi_pow_two_mul {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by sorry
