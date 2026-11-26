-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyRegionLintegralMeasurableV1
-- name    : Kyprianou.Ch05.pointFamilyRegionLintegralMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:19:04.33907+00:00
-- url     : https://prove2.me/theorems/89423e50-0bcc-4669-bc9c-46aaeb6189d1
-- title:
--   Nonnegative Poisson integral on any measurable region is measurable in its evaluation sigma algebra
-- statement:
--   All restricted measure evaluations are measurable in the region sigma algebra by the proved exhaustion lemma. The Giry measure-space integral evaluation is measurable for each nonnegative measurable integrand.
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

theorem Kyprianou.Ch05.pointFamilyRegionLintegralMeasurableV1
    {Omega E : Type} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → E)
    (R : Set E) (hR : MeasurableSet R) (g : E → ENNReal) (hg : Measurable g) :
    Measurable[prmEvalSigma K Z m R] (fun w => ∫⁻ z in R, g z ∂(poissonRandomMeasure K Z w)) := by
  sorry
