-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveStripCumulativeCadlagV1
-- name    : Kyprianou.Ch05.positiveStripCumulativeCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:33:49.397865+00:00
-- url     : https://prove2.me/theorems/a7a7f492-f20d-56b9-a021-7c7db4ae36d5
-- title:
--   Locally finite positive mark cumulative mass is monotone and cadlag
-- statement:
--   The cumulative weighted measure is monotone and finite at each finite time. Continuity from above on decreasing time strips yields right continuity, and real monotone paths have left limits.
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

theorem Kyprianou.Ch05.positiveStripCumulativeCadlagV1
    (mu : Measure (ℝ × ℝ))
    (hfin : ∀ t : NNReal, (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu) < ⊤) :
    let J := fun t : NNReal => (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu).toReal
    Monotone J ∧ IsCadlag J := by
  sorry
