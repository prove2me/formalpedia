-- Prove2me | Theorems.Thm_Kyprianou_Ch05_stableLevyDeficitOfGamma
-- name    : Kyprianou.Ch05.stableLevyDeficitOfGamma
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:58:44.068229+00:00
-- url     : https://prove2.me/theorems/0ea94673-2753-5cea-89e2-5035929d20c3
-- title:
--   Candidate stable Levy density deficit integral from Chapter 1 Gamma identity
-- statement:
--   Convert the integrable Gamma kernel to the candidate measure using withDensity and positive normalising factor.
-- source:
--   Kyprianou (2006), Exercise 5.6(i); exponential deficit and Gamma identity.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.stableLevyDeficitOfGamma
    (alpha t : Real) (ha0 : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < t)
    (hg : 0 < -Real.Gamma (-alpha))
    (hk : IntegrableOn (fun x : Real =>
      (Real.exp (-(t*x)) - 1) * x ^ (-alpha-1)) (Set.Ioi 0) ∧
      (∫ x in Set.Ioi (0 : Real),
        (Real.exp (-(t*x)) - 1) * x ^ (-alpha-1) ∂volume) =
        Real.Gamma (-alpha) * t ^ alpha) :
    let nu := ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
      (fun z : Real => ENNReal.ofReal (z ^ (-1-alpha) / (-Real.Gamma (-alpha))))
    IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) nu ∧
    (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂nu) = t ^ alpha := by
  sorry
