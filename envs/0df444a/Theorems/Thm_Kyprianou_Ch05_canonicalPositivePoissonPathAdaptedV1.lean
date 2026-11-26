-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonPathAdaptedV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonPathAdaptedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:19:01.989926+00:00
-- url     : https://prove2.me/theorems/cbceee17-191b-59d1-9af2-ee84ca47d88d
-- title:
--   Canonical uncompensated positive Poisson path is adapted to the raw evaluation filtration
-- statement:
--   The full positive strip lies inside the past region, so the restricted integral is measurable in its evaluation sigma algebra and hence in the filtration. The toReal and deterministic drift operations preserve measurability.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonPathAdaptedV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (F : Filtration NNReal inferInstance)
    (hF : ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi)
      (Iic (t : ℝ) ×ˢ univ))
    (d : ℝ) :
    Adapted F (fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) := by
  sorry
