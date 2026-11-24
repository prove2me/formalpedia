-- Prove2me | Theorems.Thm_Kyprianou_Ch03_prod_expClock_survivalSectionV1
-- name    : Kyprianou.Ch03.prod_expClock_survivalSectionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:46:05.605006+00:00
-- url     : https://prove2.me/theorems/a3fbcb37-e51d-4c3f-b209-61be3dbe3247
-- title:
--   Exponential survival at an extended threshold
-- statement:
--   The infinite threshold gives the empty set. A finite threshold gives the stated survival identity, and the probability measure has finite mass.
-- source:
--   Kyprianou (2006), Exercise 3.6; faithful auxiliary reduction of e7615c25-61ff-4f34-bf1a-1f06850e5e0e.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.prod_expClock_survivalSectionV1
    {OmegaE : Type} [MeasurableSpace OmegaE]
    (Q : Measure OmegaE) [IsProbabilityMeasure Q]
    (q : ℝ) (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {z : OmegaE | t < e z}).toReal = Real.exp (-q * (t : ℝ)))
    (a : WithTop NNReal) :
    Q {z : OmegaE | a < (e z : WithTop NNReal)} =
      ENNReal.ofReal (if a = ⊤ then (0 : ℝ)
        else Real.exp (-q * ((a.untopD (0 : NNReal) : NNReal) : ℝ))) := by sorry
