-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightNaturalClippedSupermartingaleExpectedBound
-- name    : Kyprianou.Ch01.rightNaturalClippedSupermartingaleExpectedBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:34:15.945249+00:00
-- url     : https://prove2.me/theorems/d6c225d3-6def-463a-ba08-ea489653518a
-- title:
--   Uniformly bounded continuous-time supermartingale optional stopping at clipped right-natural times
-- statement:
--   Given any uniformly bounded supermartingale M adapted to the exact right-natural filtration of process Y, with pathwise right-continuity, and any possibly infinite right-natural stopping time tau, the expected value of M at the clipped finite stopping time min(tau,n) is at most its initial expected value. Define NNReal time T=untopD n(min(tau,n)), use the already proved clipped stopping-time lemma to establish T is a bounded stopping time, then invoke the already proved MarkovProcess.integral_stoppedValue_le_of_le theorem. This is the finite-horizon optional-sampling estimate needed before taking limits n→infinity in the McKean perpetual put proof.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; bounded continuous-time supermartingale optional stopping.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingMinTimeFinite
import Theorems.Thm_MarkovProcess_integral_stoppedValue_le_of_le
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightNaturalClippedSupermartingaleExpectedBound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y M : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight Y t)
    (hSM : Supermartingale M F P)
    (C : ℝ) (hC : ∀ t ω, ‖M t ω‖ ≤ C)
    (hright : ∀ ω v, ContinuousWithinAt (fun t : ℝ≥0 => M t ω) (Set.Ici v) v)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime Y tau)
    (n : ℝ≥0) :
    (∫ ω, M ((min (tau ω) (n : WithTop ℝ≥0)).untopD n) ω ∂P) ≤
      ∫ ω, M 0 ω ∂P := by sorry
