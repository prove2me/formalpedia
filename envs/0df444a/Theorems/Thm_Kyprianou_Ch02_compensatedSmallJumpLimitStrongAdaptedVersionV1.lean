-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpLimitStrongAdaptedVersionV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpLimitStrongAdaptedVersionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:39:27.13191+00:00
-- url     : https://prove2.me/theorems/faf9feb8-cc05-4284-b254-316cc0cb6473
-- title:
--   Theorem 2.10: strongly adapted measurable modification on a common a.s. event
-- statement:
--   Recover a strongly adapted representative from the original common almost-sure uniform-on-compacts limit, equal to that limit at every time on one common full-measure event. The original transfer lemma was disproved because an arbitrary a.s. modification may be nonmeasurable. This statement explicitly constructs a measurable version before claiming any martingale property.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, measurable martingale version correction

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
theorem compensatedSmallJumpLimitStrongAdaptedVersionV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
    (M : ℝ≥0 → Ω → ℝ)
    (hzero : M 0 = fun _ => 0)
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
                    M t ω| < δ)) :
    ∃ (M' : ℝ≥0 → Ω → ℝ),
      (M' 0 = fun _ => 0) ∧
      MeasureTheory.StronglyAdapted ℱ M' ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M' t ω = M t ω) ∧
            ∀ T : ℝ≥0, 0 < T →
              ∃ ε : ℕ → ℝ,
                StrictAnti ε ∧
                (∀ n, 0 < ε n ∧ ε n < 1) ∧
                Tendsto ε Filter.atTop (nhds 0) ∧
                (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
                  ∃ n₀ : ℕ, ∀ n ≥ n₀,
                    ∀ t : ℝ≥0, t ≤ T →
                      |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                          M' t ω| < δ)
    := by sorry
end Kyprianou.Ch02
