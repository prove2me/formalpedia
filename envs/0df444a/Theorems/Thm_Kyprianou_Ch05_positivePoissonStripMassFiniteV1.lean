-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMassFiniteV1
-- name    : Kyprianou.Ch05.positivePoissonStripMassFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:19:07.688795+00:00
-- url     : https://prove2.me/theorems/f939e4b1-d498-4a3a-91b4-6476bb8b9663
-- title:
--   Poisson positive mark mass on each bounded time strip is finite almost surely
-- statement:
--   Apply the proved Chapter 2 Poisson integral integrability criterion to the nonnegative marked strip indicator, using the truncated intensity integrability lemma. Convert the finite integral to the corresponding restricted lintegral.
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

theorem Kyprianou.Ch05.positivePoissonStripMassFiniteV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (s t : ℝ) :
    ∀ᵐ w ∂Q, (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) < ⊤ := by
  sorry
