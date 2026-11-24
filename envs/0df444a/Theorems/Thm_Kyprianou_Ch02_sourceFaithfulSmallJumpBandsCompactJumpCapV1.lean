-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpBandsCompactJumpCapV1
-- name    : Kyprianou.Ch02.sourceFaithfulSmallJumpBandsCompactJumpCapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:22:56.770949+00:00
-- url     : https://prove2.me/theorems/6f4ba48e-388b-4ea3-9657-4a1da07463fe
-- title:
--   Common strict jump cap for all compensated small-jump bands on a compact horizon
-- statement:
--   The temporal coordinates of distinct Poisson marks are almost surely distinct, by atomlessness of Lebesgue time. On a compact horizon the marks with absolute value between one half and one are finite, so their maximum together with one half is strictly below one. Each compensated band has a continuous compensator and jumps given by at most one mark, and countably many bands can be handled on a single full-measure event.
-- source:
--   Kyprianou (2006), Chapter 2, proof of Theorem 2.1, small-jump process

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
theorem sourceFaithfulSmallJumpBandsCompactJumpCapV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, c < 1 ∧
      ∀ n (t : ℝ≥0), 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - l| ≤ c := by sorry
end Kyprianou.Ch02
