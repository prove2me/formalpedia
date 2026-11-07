-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat16_exp_exponent_injective
-- name    : LevyFoundations.leanlevy_chat16_exp_exponent_injective
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T12:30:26.768188+00:00
-- url     : https://prove2.me/theorems/2aca5eaa-afe7-4b33-a40b-08d98c2eb008
-- title:
--   Injectivity of the exponential Levy-Khintchine exponent on valid triples
-- statement:
--   Two valid Levy-Khintchine triples are equal if their exponentials agree at every real frequency. The source proof identifies the unique continuous logarithm normalised at zero, then recovers Gaussian variance, Levy measure and drift by smeared-measure inversion.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4: Levy/LevyKhintchineUniqueness.lean lines 526-546 (ext_of_exponent_eq) and 629-640 (existsUnique_levyKhintchineTriple).

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory

theorem LevyFoundations.leanlevy_chat16_exp_exponent_injective
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, Complex.exp (LevyFoundations.exponent T ξ) =
       Complex.exp (LevyFoundations.exponent U ξ)) :
    T = U := by sorry
