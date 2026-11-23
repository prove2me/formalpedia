-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitHasIndependentIncrementsOfMartingaleV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpUniformLimitHasIndependentIncrementsOfMartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:41:12.066833+00:00
-- url     : https://prove2.me/theorems/af63ec03-94d0-4d9a-851e-2f3c57493b17
-- title:
--   Stability of independent increments for a measurable L2 small-jump martingale limit
-- statement:
--   The limit martingale M has independent increments because its finite-region compensated-Poisson approximants have that property and their joint finite-dimensional laws converge under almost-sure uniform convergence on compact intervals. The Martingale M ℱ P hypothesis supplies the measurable adapted representative missing from an earlier disproved unrestricted limit statement. Use characteristic-function convergence for any finite vector of time increments, independent Poisson disjoint regions, and stability of product characteristic functions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10: stochastic limit Lévy increments.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedSmallJumpUniformLimitHasIndependentIncrementsOfMartingaleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hzero : M 0 = fun _ => 0)
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
    (hmart : MeasureTheory.Martingale M ℱ P)
    (hL2 : ∀ t, MemLp (M t) 2 P)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)
  ) :
    ProbabilityTheory.HasIndependentIncrements M P
    := by sorry
end Kyprianou.Ch02
