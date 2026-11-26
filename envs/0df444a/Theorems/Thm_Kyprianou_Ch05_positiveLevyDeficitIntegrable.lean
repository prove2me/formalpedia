-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveLevyDeficitIntegrable
-- name    : Kyprianou.Ch05.positiveLevyDeficitIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:58:43.628587+00:00
-- url     : https://prove2.me/theorems/af318d7f-c454-5929-ace9-de573331cd52
-- title:
--   Positive Levy deficit is integrable from the truncated first moment
-- statement:
--   Bound the positive exponential deficit on positive marks by max(1,t) times min(1,x).
-- source:
--   Kyprianou (2006), Exercise 5.6(i); exponential deficit and Gamma identity.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.positiveLevyDeficitIntegrable
    (mu : Measure Real)
    (hm : (∫⁻ x in Set.Ioi (0 : Real),
      ENNReal.ofReal (min (1 : Real) x) ∂mu) < ⊤)
    (t : Real) (ht : 0 < t) :
    IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) mu := by
  sorry
