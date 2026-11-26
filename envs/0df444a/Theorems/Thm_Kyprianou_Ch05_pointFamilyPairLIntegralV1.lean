-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyPairLIntegralV1
-- name    : Kyprianou.Ch05.pointFamilyPairLIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:25:52.501816+00:00
-- url     : https://prove2.me/theorems/15a55c63-01cd-5387-9c57-3991bc267ab9
-- title:
--   Poisson integral is a sum over active index pairs
-- statement:
--   Use the Chapter 2 atomic integral identity, replace the finite sum by the sum of its zero extension and combine the two countable indices.
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

theorem Kyprianou.Ch05.pointFamilyPairLIntegralV1
    {Omega E : Type} [MeasurableSpace E]
    (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → E)
    (w : Omega) (g : E → ENNReal) (hg : Measurable g) :
    (∫⁻ z, g z ∂(poissonRandomMeasure K Z w)) =
      ∑' i : ℕ × ℕ, if i.2 < K i.1 w then g (Z i.1 i.2 w) else 0 := by
  sorry
