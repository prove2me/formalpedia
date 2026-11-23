-- Prove2me | Theorems.Thm_Kyprianou_compensatedBandIsL2MartingaleCorrected
-- name    : Kyprianou.compensatedBandIsL2MartingaleCorrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:19:52.594539+00:00
-- url     : https://prove2.me/theorems/7e5adf31-3c73-406e-bb59-84b22f42d4ab
-- title:
--   Lemma 2.9: compensated finite-band martingale (corrected)
-- statement:
--   The finite-band compensated Poisson process is an L² martingale in an appropriate filtration, for each 0<ε<1.
--   Corrected source-faithful assumptions and pathwise filtration.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem compensatedBandIsL2MartingaleCorrected
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale
        (compensatedSmallJumpBand P levyMeasure N ε) ℱ P ∧
      ∀ t : ℝ≥0,
        MemLp (compensatedSmallJumpBand P levyMeasure N ε t) 2 P
      := by sorry
end Kyprianou
