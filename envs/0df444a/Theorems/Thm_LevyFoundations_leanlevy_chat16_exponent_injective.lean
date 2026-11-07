-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_injective
-- name    : LevyFoundations.leanlevy_chat16_exponent_injective
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T12:48:09.528133+00:00
-- url     : https://prove2.me/theorems/46afeb62-bc66-488d-9b50-dec2e28de2a4
-- title:
--   Recover a Levy-Khintchine triple from its exponent
-- statement:
--   A valid Levy-Khintchine triple is uniquely determined by its complex characteristic exponent. The source obtains equal finite smeared measures by Fourier inversion, then recovers the Gaussian atom, jump measure and drift.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 526-546, LevyKhintchineTriple.ext_of_exponent_eq.

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
open MeasureTheory

theorem LevyFoundations.leanlevy_chat16_exponent_injective
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, LevyFoundations.exponent T ξ = LevyFoundations.exponent U ξ) :
    T = U := by sorry
