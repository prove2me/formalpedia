-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpLimitIsLevyOfMartingaleV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpLimitIsLevyOfMartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:36:30.311584+00:00
-- url     : https://prove2.me/theorems/5af2918b-08c7-443e-af0e-a46b925db6b4
-- title:
--   Levy increments and cadlag limit for a measurable small-jump martingale representative
-- statement:
--   If a specific compensated small-jump limit is a martingale for the completed natural Poisson filtration and L2 at every time, with M0=0 and local uniform convergence almost surely, prove its Levy property by passing independent and stationary increments of finite-band Poisson processes through finite-dimensional convergence and obtaining cadlag paths from the already proved uniform limit lemma. The added martingale hypothesis supplies the ambient measurability absent from the disproved generic limit implication.
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
theorem compensatedSmallJumpLimitIsLevyOfMartingaleV1
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
    ProbabilityTheory.IsLevyProcess M P
    := by sorry
end Kyprianou.Ch02
