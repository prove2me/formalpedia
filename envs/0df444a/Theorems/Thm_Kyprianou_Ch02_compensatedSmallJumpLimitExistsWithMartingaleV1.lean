-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpLimitExistsWithMartingaleV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpLimitExistsWithMartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:36:32.575707+00:00
-- url     : https://prove2.me/theorems/326b172f-6c99-459b-9e60-47e0d692bdb4
-- title:
--   Construct measurable adapted L2 martingale representative of the compensated small-jump uniform limit
-- statement:
--   Construct one joint witness M and completed natural Poisson filtration for which M vanishes at 0, is a true strongly-adapted L2 martingale, and finite-band compensated Poisson sums converge uniformly almost surely along a subsequence on each compact interval. Crucially the martingale and representative properties are established together, unlike the disproved claim that every arbitrary almost-surely equivalent limit M is a martingale. Prove by choosing the canonical measurable limit of L2-Cauchy band martingales, with completion handling null sets.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10: Poisson small-jump compensated martingale limit.

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
theorem compensatedSmallJumpLimitExistsWithMartingaleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      (M 0 = fun _ => 0) ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
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
      := by sorry
end Kyprianou.Ch02
