-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpLimitCompletedL2VersionV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpLimitCompletedL2VersionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:39:26.456136+00:00
-- url     : https://prove2.me/theorems/227ad44c-61cf-430d-8ff3-7a8ebadceecb
-- title:
--   Theorem 2.10: existence of a completed-filtration L²-martingale version
-- statement:
--   Use the measurable version theorem and fixed-filtration finite-band L² martingale transfer to obtain a suitable martingale representative of the small-jump path without asserting that every arbitrary null-set modification is a martingale.
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
theorem compensatedSmallJumpLimitCompletedL2VersionV1
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
      MeasureTheory.Martingale M' ℱ P ∧
      (∀ t : ℝ≥0, MemLp (M' t) 2 P) ∧
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
