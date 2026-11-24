-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpJumpBoundOfUniformV2
-- name    : Kyprianou.Ch02.sourceFaithfulSmallJumpJumpBoundOfUniformV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:01:11.377807+00:00
-- url     : https://prove2.me/theorems/9bfaf8cd-3ed3-4a29-a4e1-767c5773d20d
-- title:
--   The compact-uniform compensated small-jump limit has jumps of absolute size strictly less than one at every po
-- statement:
--   The compact-uniform compensated small-jump limit has jumps of absolute size strictly less than one at every positive jump time, almost surely.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, Lévy–Itô component verification

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem sourceFaithfulSmallJumpJumpBoundOfUniformV2
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hM : ProbabilityTheory.IsLevyProcess M P)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ))
 :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ∀ l : ℝ,
        Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds l) →
        (M t ω ≠ l → |M t ω - l| < 1)
    := by sorry
end Kyprianou.Ch02
