-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveLevyMeasureEqOfDeficitPlusDrift
-- name    : Kyprianou.Ch05.positiveLevyMeasureEqOfDeficitPlusDrift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:58:46.265033+00:00
-- url     : https://prove2.me/theorems/de54a17d-3798-45b4-abc2-5012664172b8
-- title:
--   Positive jump measure uniqueness from exponential deficits up to drift
-- statement:
--   Take second forward differences in t to cancel drift. The resulting transforms identify the measures weighted by the positive squared deficit on positive marks. Apply general Laplace measure uniqueness, then cancel the positive density using the zero mass outside positive marks.
-- source:
--   Kyprianou (2006), Exercise 5.6(i); exponential deficit and Gamma identity.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.positiveLevyMeasureEqOfDeficitPlusDrift
    (mu nu : Measure Real) (d : Real)
    (hm : mu (Set.Iic (0 : Real)) = 0)
    (hn : nu (Set.Iic (0 : Real)) = 0)
    (hmi : ∀ t : Real, 0 < t →
      IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) mu)
    (hni : ∀ t : Real, 0 < t →
      IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) nu)
    (heq : ∀ t : Real, 0 < t →
      d*t + (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂mu) =
      (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂nu)) :
    mu = nu := by
  sorry
