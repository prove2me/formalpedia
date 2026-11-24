-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCompensatedBandJumpCapGivenMarkCutoffV1
-- name    : Kyprianou.Ch02.prmCompensatedBandJumpCapGivenMarkCutoffV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:51:53.795824+00:00
-- url     : https://prove2.me/theorems/63484a05-5a82-4011-9b8f-2b0eaa69335d
-- title:
--   Each finite compensated band obeys any common mark cutoff on a compact window
-- statement:
--   Each finite compensated band obeys any common mark cutoff on a compact window
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

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
theorem prmCompensatedBandJumpCapGivenMarkCutoffV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, 0 ≤ c →
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0 →
      ∀ t : ℝ≥0, 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P ν N e t ω - l| ≤ c := by sorry
end Kyprianou.Ch02
