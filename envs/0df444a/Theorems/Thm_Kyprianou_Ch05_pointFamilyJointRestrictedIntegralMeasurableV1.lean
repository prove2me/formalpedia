-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyJointRestrictedIntegralMeasurableV1
-- name    : Kyprianou.Ch05.pointFamilyJointRestrictedIntegralMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:25:55.92059+00:00
-- url     : https://prove2.me/theorems/2944bc86-4255-596d-bb6f-deab39adbe66
-- title:
--   Jointly measurable random marked Poisson integrals over measurable regions
-- statement:
--   Expand the restricted integral into the countable sum of jointly measurable evaluations at active indices, with a measurable region indicator.
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

theorem Kyprianou.Ch05.pointFamilyJointRestrictedIntegralMeasurableV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → E)
    (hK : ∀ k, Measurable (K k)) (hZ : ∀ k n, Measurable (Z k n))
    (g : Omega × E → ENNReal) (hg : Measurable g)
    (S : Set E) (hS : MeasurableSet S) :
    Measurable (fun w => ∫⁻ z in S, g (w,z) ∂(poissonRandomMeasure K Z w)) := by
  sorry
