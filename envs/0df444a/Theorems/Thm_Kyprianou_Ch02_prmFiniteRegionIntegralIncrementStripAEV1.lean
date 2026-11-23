-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIntegralIncrementStripAEV1
-- name    : Kyprianou.Ch02.prmFiniteRegionIntegralIncrementStripAEV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:13:29.037355+00:00
-- url     : https://prove2.me/theorems/75a424d4-700c-41cf-815a-1c899e279684
-- title:
--   Finite-activity marked Poisson integral increments equal integrals over the intervening time strip simultaneously
-- statement:
--   On one common conull event, for all 0≤s≤t, the difference of the cumulative marked integrals on (0,t] and (0,s] equals the marked integral on (s,t]. Use the already Proved finite-window Dirac representation to establish simultaneous finite integrability on bounded windows, then apply additivity over the disjoint Borel time strips. Equality for all times simultaneously is essential for subsequent random-vector independence.
-- source:
--   Kyprianou (2006), Eq. (2.3), independent-increments branch, actual LevyStochCalc PoissonRandomMeasure with independent_disjoint and measurable_eval fields; mission ed6e9edb-945b-4dc1-bb4b-3eed54f89dd0.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionIntegralIncrementStripAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ProbabilityTheory.increment (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) s t ω =
        ∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω) := by sorry
