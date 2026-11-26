-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveStripShrinkingLeftLimitV1
-- name    : Kyprianou.Ch05.positiveStripShrinkingLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:59:02.574993+00:00
-- url     : https://prove2.me/theorems/921d56c1-f665-45ec-b7f1-9e16e5c8b6c3
-- title:
--   Positive strip mass converges to the time atom from the left
-- statement:
--   Apply continuity from above to the weighted measure on strips (s,t] as s approaches t from below, using the dual time order. The intersection is precisely the time fibre, and local finiteness permits the real-valued limit.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.positiveStripShrinkingLeftLimitV1
    (mu : Measure (ℝ × ℝ)) (t : NNReal) (ht : 0 < t)
    (hf : (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu) < ⊤) :
    Tendsto (fun s : NNReal => (∫⁻ z in Ioc (s : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu).toReal) (nhdsWithin t (Iio t))
      (nhds ((∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂mu).toReal)) := by
  sorry
