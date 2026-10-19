-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_finite
-- name    : MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T05:37:05.326987+00:00
-- url     : https://prove2.me/theorems/9bbcd4d6-8ba2-466a-9613-7a38c30e01b6
-- title:
--   Both actual good-prime integral norm maps are finite
-- statement:
--   Let $q$ be a prime with $q \nmid104$ and $q\ne19$. On the same selected local Picard model over $\mathbb Z_{(q)}$, let $\Pi$ and $\overline\Pi$ be the unique integral extensions of the two actual rational norm maps. Both are finite morphisms:
--
--   $$\Pi\text{ is finite}\qquad\text{and}\qquad\overline\Pi\text{ is finite}.$$
--
--   This supplies finiteness for the actual local norm maps used in good-prime inertia arguments; it is not a finiteness assumption on an independently supplied morphism.
-- source:
--   MazurTheorem, Order13GoodPrimeIntegralNormFinite.lean, original actual integral norm theorem and all hypotheses; full source SHA-256 470962a3a755b2c5881c52c35ab789e65d2642383dfdf6dab6584cbe0d71f3f8, Apache-2.0. Official Anthropic FLT local group interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
open MazurTransfer
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeIntegralNormExtensions

theorem MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    IsFinite (integralPi q hq).val ∧ IsFinite (integralPiConjugate q hq).val := by sorry
