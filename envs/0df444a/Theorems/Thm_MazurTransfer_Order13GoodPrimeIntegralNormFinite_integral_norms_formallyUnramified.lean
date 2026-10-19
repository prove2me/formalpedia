-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_formallyUnramified
-- name    : MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T05:46:36.85063+00:00
-- url     : https://prove2.me/theorems/3d8b9f50-f50a-4314-af59-f5b2ab058a3d
-- title:
--   Both actual good-prime integral norm maps are formally unramified
-- statement:
--   Let $q$ be a prime not dividing $104$ and different from $19$. Let $\Pi$ and $\overline\Pi$ be the actual norm endomorphisms of the same selected local Picard model over $\mathbb Z_{(q)}$. Then
--
--   $$\Pi\text{ and }\overline\Pi\text{ are formally unramified}.$$
--
--   The property holds for these integral extensions themselves and supplies the unramified-map hypothesis needed to fix actual norm lifts under valuation inertia.
-- source:
--   MazurTheorem, Order13GoodPrimeIntegralNormFinite.lean, original actual integral norm theorem and all hypotheses; full source SHA-256 470962a3a755b2c5881c52c35ab789e65d2642383dfdf6dab6584cbe0d71f3f8, Apache-2.0. Official Anthropic FLT local group interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
open MazurTransfer
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeIntegralNormExtensions

theorem MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    FormallyUnramified (integralPi q hq).val ∧
      FormallyUnramified (integralPiConjugate q hq).val := by sorry
