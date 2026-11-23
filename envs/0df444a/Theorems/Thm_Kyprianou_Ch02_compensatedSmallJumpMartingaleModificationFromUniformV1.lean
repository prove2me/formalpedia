-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpMartingaleModificationFromUniformV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpMartingaleModificationFromUniformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:45:45.5062+00:00
-- url     : https://prove2.me/theorems/391e0592-6ea7-41dd-8b88-13b4bb1e1f89
-- title:
--   Measurable martingale modification of an almost-surely uniform Poisson small-jump limit
-- statement:
--   Given a completed Poisson natural filtration and an arbitrary M0 that is an almost-sure uniform limit of compensated small-jump bands on compact time intervals, construct a version M which is an adapted true martingale, has finite second moment at every time, and agrees with M0 simultaneously for all nonnegative times outside a single probability-zero set. The requirement to choose a measurable representative is essential, as the naive assertion that M0 itself is a martingale has a Prove2Me counterexample. Use the proved finite-band L2 martingale theorem in the same filtration, uniform second-moment bounds, L1 convergence, conditional-expectation continuity, and measurable versions of the pointwise limit to establish the result.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, compensated small-jump martingale L2 limit and regular version.

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
theorem compensatedSmallJumpMartingaleModificationFromUniformV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
    (M₀ : ℝ≥0 → Ω → ℝ)
    (hzero : M₀ 0 = fun _ => 0)
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
                    M₀ t ω| < δ)
  ) :
    ∃ (M : ℝ≥0 → Ω → ℝ),
      (M 0 = fun _ => 0) ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = M₀ t ω)
    := by sorry
end Kyprianou.Ch02
