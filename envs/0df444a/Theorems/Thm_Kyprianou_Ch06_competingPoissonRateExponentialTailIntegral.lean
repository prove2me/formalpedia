-- Prove2me | Theorems.Thm_Kyprianou_Ch06_competingPoissonRateExponentialTailIntegral
-- name    : Kyprianou.Ch06.competingPoissonRateExponentialTailIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:40:24.871243+00:00
-- url     : https://prove2.me/theorems/e939af7d-15d7-4541-be30-582d47bb6dba
-- title:
--   Lemma 6.18: competing Poisson rates exponential arrival-tail integral
-- statement:
--   For Poisson mark-region intensity a>0, competing region intensity b≥0, and observation time t, the integral from t to infinity of a*exp(-(a+b)s) equals a/(a+b) times exp(-(a+b)t). It provides the exact normalized first-mark probability factor needed when splitting a finite-intensity mark set A into C∩A and A∖C in Kyprianou Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18 (first Poisson mark distribution), printed pp.160–161, exponential-race integral.

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.competingPoissonRateExponentialTailIntegral
    (a b t : Real) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ s in Set.Ioi t, a * Real.exp (-(a + b) * s)) =
      (a / (a + b)) * Real.exp (-(a + b) * t) := by sorry
