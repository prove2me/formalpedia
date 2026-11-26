-- Prove2me | Theorems.Thm_MellinDuality_eq_of_pow_four_eq_one
-- name    : MellinDuality.eq_of_pow_four_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:42:46.586268+00:00
-- url     : https://prove2.me/theorems/6d955641-8255-4141-bdb8-640ebff97a94
-- title:
--   Mellin Duality: eq of pow four eq one
-- statement:
--   The fourth roots of unity in `ℤ[i]` are `1, i, -1, -i`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L44-L54
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean#L44-L54

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality

theorem MellinDuality.eq_of_pow_four_eq_one {x : GaussianInt} (h : x ^ 4 = 1) :
    x = 1 ∨ x = gi ∨ x = -1 ∨ x = -gi := by sorry
