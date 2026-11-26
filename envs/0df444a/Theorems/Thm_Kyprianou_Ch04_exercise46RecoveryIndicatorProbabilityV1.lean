-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryIndicatorProbabilityV1
-- name    : Kyprianou.Ch04.exercise46RecoveryIndicatorProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:05:45.40802+00:00
-- url     : https://prove2.me/theorems/9d94ad45-eeea-518f-80a7-87ae9e8cc76e
-- title:
--   Zero-discount recovery transform gives finite recovery probability
-- statement:
--   The zero-discount killed passage payoff is the indicator of a finite recovery clock, so its integral equals the probability of recovery.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RecoveryIndicatorProbabilityV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → WithTop NNReal) (hB : Measurable B)
    (q : Real)
    (hTransform : (∫ w, if B w = ⊤ then (0 : Real) else
      Real.exp (-(0 : Real) * (((B w).untopD 0 : NNReal) : Real)) ∂P) = q) :
    (P {w | B w ≠ ⊤}).toReal = q := by
  sorry
