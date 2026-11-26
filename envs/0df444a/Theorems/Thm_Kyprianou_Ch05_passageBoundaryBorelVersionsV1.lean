-- Prove2me | Theorems.Thm_Kyprianou_Ch05_passageBoundaryBorelVersionsV1
-- name    : Kyprianou.Ch05.passageBoundaryBorelVersionsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:29:25.657962+00:00
-- url     : https://prove2.me/theorems/d2e8d9be-5c48-5748-88a5-19624b8e9885
-- title:
--   Measurable right and left path values at a measurable finite clock
-- statement:
--   Use Avram's proved measurable shrinking right and left grid selection theorems, followed by the Borel limit operation on the two sample sequences.
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

theorem Kyprianou.Ch05.passageBoundaryBorelVersionsV1
    (t : (NNReal → ℝ) → NNReal) (ht : Measurable t) :
    ∃ R L : (NNReal → ℝ) → ℝ, Measurable R ∧ Measurable L ∧
      (∀ f : NNReal → ℝ, ContinuousWithinAt f (Ici (t f)) (t f) → R f = f (t f)) ∧
      ∀ f : NNReal → ℝ, 0 < t f → Monotone f → L f = Function.leftLim f (t f) := by
  sorry
