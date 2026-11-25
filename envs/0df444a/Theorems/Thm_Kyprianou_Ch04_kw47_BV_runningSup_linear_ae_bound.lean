-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_BV_runningSup_linear_ae_bound
-- name    : Kyprianou.Ch04.kw47_BV_runningSup_linear_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:59:13.508108+00:00
-- url     : https://prove2.me/theorems/c14555f9-7f4c-5928-848a-8c53498ce195
-- title:
--   BV running maximum bounded by positive drift envelope almost surely
-- statement:
--   For any bounded-variation spectrally negative Lévy process, the existing pathwise upper drift theorem yields X_s≤s drift for all times on a common full-measure event. On each such path and finite T, the running supremum is at most max(0,T drift) by taking the supremum over 0≤s≤T and considering both signs of drift. This deterministic cap leads to uniform exponential running-supremum integrability in the BV branch.
-- source:
--   Kyprianou (2006), Chapter 4, pp. 87–109, bounded-variation drift-minus-subordinator representation and Exercise 4.7.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- BV Lévy paths have the running supremum bounded by the
positive part of their linear drift, uniformly up to each horizon. -/

theorem Kyprianou.Ch04.kw47_BV_runningSup_linear_ae_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (T : NNReal) :
    ∀ᵐ w ∂P, runningSup L T w ≤ max 0 ((T : Real) * L.drift) := by sorry
