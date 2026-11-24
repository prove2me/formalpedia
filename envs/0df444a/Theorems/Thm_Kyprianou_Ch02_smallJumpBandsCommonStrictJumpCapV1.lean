-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpBandsCommonStrictJumpCapV1
-- name    : Kyprianou.Ch02.smallJumpBandsCommonStrictJumpCapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:21:09.052542+00:00
-- url     : https://prove2.me/theorems/21b1ad89-fadc-4492-a6a3-5b41550c2af6
-- title:
--   Finite compensated bands share a strict pathwise jump-size cap on a compact time horizon
-- statement:
--   For any countable collection of positive cutoffs below one and a fixed finite horizon, almost every PRM path has a common jump-size bound c strictly less than one for all bands. The finite number of marks with absolute size at least one-half gives a strict maximum below one; absence of simultaneous marks follows from diffuse Lebesgue time intensity on each finite band. Compensation is continuous.
-- source:
--   Kyprianou (2006), Theorem 2.1 and Chapter 2 finite-band approximation; supporting lemma

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

open scoped Topology

namespace Kyprianou.Ch02
theorem smallJumpBandsCommonStrictJumpCapV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, c < 1 ∧
      ∀ (n : ℕ) (t : ℝ≥0), 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - l| ≤ c
    := by sorry
end Kyprianou.Ch02
