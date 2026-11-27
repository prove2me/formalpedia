-- Prove2me | Theorems.Thm_GRH_centered_moebius_iff_summable_one_class_prime_deficits_at_factorial_levels
-- name    : GRH.centered_moebius_iff_summable_one_class_prime_deficits_at_factorial_levels
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:22:03.722539+00:00
-- url     : https://prove2.me/theorems/773d96c2-abbf-51d4-9925-7ca78658274a
-- title:
--   Dirichlet GRH strength of summable one-class prime deficits on factorial moduli
-- statement:
--   The all-moduli centered Möbius bound and the earlier pointwise cofinal prime bound are each equivalent to convergence of the weighted positive prime deficits on cofinally many factorial levels. If the centered bound fails, every sufficiently large level gives divergence at the required exponent and convergence at exponent 1.
-- source:
--   The exact Möbius target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Its previously verified one-class reduction is https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800 . The fixed-modulus zero-free equivalence is https://prove2.me/submissions/c72da535-7bc5-423b-a138-a1ebdb0e7d0b .

import Definitions.Def_GRH_PrimeDeficitMean

open MeasureTheory Set Filter Topology ArithmeticFunction GRH.PrimeDeficitMean GRH.SplitPrimeLower GRH.OneSidedMoebius GRH.FactorialMoebius

theorem GRH.centered_moebius_iff_summable_one_class_prime_deficits_at_factorial_levels : (centeredBound ↔ cofinalMean) ∧ (cofinalPrimeLower ↔ cofinalMean) ∧
    (¬centeredBound → ∃ B : ℕ, ∀ k : ℕ, B≤k →
      ¬ Summable (deficitTerm (level k) (exponent k)) ∧ Summable (deficitTerm (level k) 1)) := by sorry
