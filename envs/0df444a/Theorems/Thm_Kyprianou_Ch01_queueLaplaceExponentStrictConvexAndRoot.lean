-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponentStrictConvexAndRoot
-- name    : Kyprianou.Ch01.queueLaplaceExponentStrictConvexAndRoot
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:23:13.568394+00:00
-- url     : https://prove2.me/theorems/b284c2f7-67e4-4cda-a713-7bf561654166
-- title:
--   Exercise 1.9(i): strict convexity and unique positive Cramér root of the queue exponent
-- statement:
--   Source Exercise 1.9(i): the M/G/1 queue driving Lévy exponent ψ(θ)=θ−λ∫(1−e^{−θx})F(dx) for θ≥0 is strictly convex, ψ(0)=0, ψ(θ)→+∞, and it admits exactly one positive zero θ* if and only if λμ>1. The condition F positive and finite first moment ensures ψ'(0+)=1−λμ and rules out degenerate zero-size claims. Neither positivity nor uniqueness of the root is assumed. This supports Theorem 1.11's overloaded idle-time law.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), printed p. 31.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponentStrictConvexAndRoot
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (queueLaplaceExponent rate F) ∧
    queueLaplaceExponent rate F 0 = 0 ∧
    Tendsto (queueLaplaceExponent rate F) atTop atTop ∧
    ((∃ theta : ℝ, 0 < theta ∧
      queueLaplaceExponent rate F theta = 0) ↔
        1 < (rate : ℝ) * mu) ∧
    (∀ theta theta' : ℝ,
      0 < theta → 0 < theta' →
      queueLaplaceExponent rate F theta = 0 →
      queueLaplaceExponent rate F theta' = 0 →
      theta = theta') := by
  sorry
