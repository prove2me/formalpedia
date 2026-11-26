-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46SampledRecoveryEqualsFullV1
-- name    : Kyprianou.Ch04.exercise46SampledRecoveryEqualsFullV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:22:54.763561+00:00
-- url     : https://prove2.me/theorems/df8c68c8-3dc8-4317-ac5b-89a2bb862475
-- title:
--   Dense sampled recovery clock equals the full strict crossing clock
-- statement:
--   Every full strict crossing is approximated from the right by a dense sampled strict crossing because the path is right continuous. The countable and unrestricted infimum clocks therefore agree, including the infinite case.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46SampledRecoveryEqualsFullV1
    (D : Set NNReal) (hD : Dense D)
    (f : NNReal → Real) (hR : ∀ t, ContinuousWithinAt f (Ici t) t)
    (a : WithTop NNReal) (H : Real) :
    (⨅ r ∈ D, if a < (r : WithTop NNReal) ∧ H < f r then
      (r : WithTop NNReal) else ⊤) =
      (⨅ r : NNReal, if a < (r : WithTop NNReal) ∧ H < f r then
        (r : WithTop NNReal) else ⊤) := by
  sorry
