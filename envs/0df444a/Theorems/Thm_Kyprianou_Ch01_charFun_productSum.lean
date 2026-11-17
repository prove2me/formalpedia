-- Prove2me | Theorems.Thm_Kyprianou_Ch01_charFun_productSum
-- name    : Kyprianou.Ch01.charFun_productSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:55:49.745658+00:00
-- url     : https://prove2.me/theorems/281bded9-3e65-4923-bc44-8cab3b00412c
-- title:
--   Product-probability independent-sum characteristic-function identity on the real line
-- statement:
--   For arbitrary independent real-valued coordinates on a product probability space with marginal probability measures mu and nu, the characteristic function of the image of their sum is exactly the product of their marginal characteristic functions at every real frequency. This is a direct pinned-Mathlib corollary needed to combine the pure-jump Lévy and scaled Brownian components in Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Mathlib pinned revision 0df444a360eaa60ab8c11dca51a86af692955474, ProbabilityTheory.charFun_map_add_prod_eq_mul, Mathlib.Probability.Independence.CharacteristicFunction; Kyprianou (2006), Chapter 1 Lévy–Khintchine process existence theorem.

import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.charFun_productSum
    (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (xi : ℝ) :
    charFun ((mu.prod nu).map (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      charFun mu xi * charFun nu xi := by
  sorry
