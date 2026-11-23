-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpStronglyAdaptedVersionOfUniformLimitV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpStronglyAdaptedVersionOfUniformLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:48:11.260802+00:00
-- url     : https://prove2.me/theorems/9e43747d-94f4-4ffd-93f6-c4a1fffa9866
-- title:
--   Construct a strongly adapted modification of a Poisson small-jump uniform limit
-- statement:
--   Given an arbitrary almost-surely locally uniform limit M0 of KLS finite-band compensated Poisson processes, construct a version M which starts at zero, is strongly adapted to the completed natural Poisson filtration, and equals M0 for all times simultaneously outside one P-null event. Construct a version measurable with respect to past-count evaluations by a countable-time, measurable convergence set and an adapted pointwise limit selection, using the completed filtration to repair exceptional sets. This source-faithful helper isolates exactly the measurable-representative issue behind the Disproved older generic L2 martingale theorem.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, measurable càdlàg modification of compensated small-jump limit.

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
theorem compensatedSmallJumpStronglyAdaptedVersionOfUniformLimitV1
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
      MeasureTheory.StronglyAdapted ℱ M ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = M₀ t ω)
    := by sorry
end Kyprianou.Ch02
