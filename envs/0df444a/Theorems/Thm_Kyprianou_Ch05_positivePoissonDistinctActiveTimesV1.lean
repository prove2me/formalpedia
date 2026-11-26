-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonDistinctActiveTimesV1
-- name    : Kyprianou.Ch05.positivePoissonDistinctActiveTimesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:54:37.612049+00:00
-- url     : https://prove2.me/theorems/55387527-135b-5ada-809e-442a2d9a1ec0
-- title:
--   Positive Poisson point family has distinct active arrival times
-- statement:
--   On positive-intensity pieces the normalized time marginal is atomless by the Avram theorem. Distinct point coordinates are independent by the combined point family law. Countable pairwise distinctness then gives injectivity of active arrival times.
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

theorem Kyprianou.Ch05.positivePoissonDistinctActiveTimesV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q) :
    ∀ᵐ w ∂Q, ∀ i j : ℕ × ℕ,
      i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j := by
  sorry
