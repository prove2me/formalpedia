-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46SampledRecoveryClockV1
-- name    : Kyprianou.Ch04.exercise46SampledRecoveryClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:24:13.071197+00:00
-- url     : https://prove2.me/theorems/ced53e39-6909-5c10-8aee-c9c51f2fbe4c
-- title:
--   Countable sampled recovery clock is a stopping time
-- statement:
--   Each sampled clock equals its deterministic sample time on the measurable recovery test and infinity otherwise. It is a stopping time. A countable infimum of these clocks is a stopping time for the right-continuous filtration.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46SampledRecoveryClockV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (D : Set NNReal) (hD : D.Countable) :
    IsStoppingTime G.rightCont (fun w =>
      ⨅ r ∈ D, if A w < (r : WithTop NNReal) ∧ (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤) := by
  sorry
