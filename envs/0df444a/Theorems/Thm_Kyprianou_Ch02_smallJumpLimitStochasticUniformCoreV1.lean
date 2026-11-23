-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpLimitStochasticUniformCoreV1
-- name    : Kyprianou.Ch02.smallJumpLimitStochasticUniformCoreV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:13:04.105196+00:00
-- url     : https://prove2.me/theorems/8fea329a-eac9-4934-aecf-f879509f7696
-- title:
--   Theorem 2.10: Lévy L2 martingale with deterministic uniform subsequences
-- statement:
--   Construct the small-jump limit M jointly with its completed Poisson filtration, Levy-process, martingale and L2 properties, and almost-sure uniform finite-horizon approximations. Path regularity and jump countability are delegated to separate deterministic lemmas.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, deterministic uniform-limit argument

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
theorem smallJumpLimitStochasticUniformCoreV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      ProbabilityTheory.IsLevyProcess M P ∧
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
