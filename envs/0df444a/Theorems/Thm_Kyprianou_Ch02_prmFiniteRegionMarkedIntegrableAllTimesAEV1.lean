-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegrableAllTimesAEV1
-- name    : Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:19:30.149609+00:00
-- url     : https://prove2.me/theorems/5d3be3ac-52e6-4886-b600-e3c7a921746c
-- title:
--   A finite-activity Poisson marked integral is integrable on every bounded time window, simultaneously almost surely
-- statement:
--   The marked real-coordinate integrand is integrable over every bounded time interval (0,t]×B on one conull event, even without any finite first moment of ν on B. Use the previously Proved Kyprianou.Ch02.prmFiniteWindowDiracLawV1, a common conull event of locally finite atomic support for integer horizons, and monotonicity of integrability on subsets.
-- source:
--   Kyprianou (2006) Eq. (2.3), Lévy large-jump component, finite-activity PRM

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) (N.N ω) := by sorry
