-- Prove2me | Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3
-- name    : Kyprianou.finiteRegionPoissonIntegralCh02V3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:21:31.907692+00:00
-- url     : https://prove2.me/theorems/38df877c-0872-40d5-8b33-bbad3487ba47
-- title:
--   Lemma 2.8: finite-region Poisson integral gives a compound-Poisson Lévy process
-- statement:
--   Finite-intensity Poisson jump integration produces a compound-Poisson Lévy component whose rate is ν(B), jump law is ν restricted to B normalised by ν(B) whenever ν(B)>0, and whose characteristic exponent is the Poisson integral exponent. Includes the zero-intensity zero-process case as a useful extension.
-- source:
--   Kyprianou (2006), Lemma 2.8, pp. 44-45

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou

theorem finiteRegionPoissonIntegralCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)
      := by sorry

end Kyprianou
