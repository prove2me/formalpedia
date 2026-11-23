-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralCadlagAEV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonIntegralCadlagAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:00:05.246417+00:00
-- url     : https://prove2.me/theorems/bac8edbf-fc85-46c9-a22d-906bae94fa75
-- title:
--   Lemma 2.8: Almost-sure cadlag paths of the finite-region Poisson mark integral
-- statement:
--   Almost-sure cadlag paths of the finite-region Poisson mark integral. Use finite atomicity of every bounded time strip and countable integer-horizon exhaustion.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8; direct decomposition of canonical finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47).

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonIntegralCadlagAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by sorry
end Kyprianou.Ch02
