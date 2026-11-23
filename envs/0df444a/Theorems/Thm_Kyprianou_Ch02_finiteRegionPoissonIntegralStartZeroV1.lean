-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralStartZeroV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonIntegralStartZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:59:51.973467+00:00
-- url     : https://prove2.me/theorems/b5d49b49-dafa-4324-9a99-227137cda5d9
-- title:
--   Lemma 2.8: The finite-region Poisson integral starts at zero pointwise, since the time interval (0,0] is empty
-- statement:
--   The finite-region Poisson integral starts at zero pointwise, since the time interval (0,0] is empty.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8; direct decomposition of canonical finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonIntegralStartZeroV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (0 : ℝ) ×ˢ B), z.2 ∂(N.N ω)) =
      (fun _ : Ω => (0 : ℝ)) := by sorry
end Kyprianou.Ch02
