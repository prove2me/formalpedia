-- Prove2me | Theorems.Thm_Kyprianou_compensatedBandIsL2Martingale
-- name    : Kyprianou.compensatedBandIsL2Martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T11:14:06.716643+00:00
-- url     : https://prove2.me/theorems/dc8a81ae-7af7-4dec-9dd1-fdda43aad359
-- title:
--   Lemma 2.9: compensated finite-band martingale
-- statement:
--   The finite-band compensated Poisson process is an L² martingale in an appropriate filtration, for each 0<ε<1.
-- source:
--   Kyprianou (2006), Lemma 2.9 and Eq. (2.18), pp. 45–47, 52

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
theorem compensatedBandIsL2Martingale
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      MeasureTheory.Martingale
        (compensatedSmallJumpBand P levyMeasure N ε) ℱ P ∧
      ∀ t : ℝ≥0,
        MemLp (compensatedSmallJumpBand P levyMeasure N ε t) 2 P
      := by sorry
end Kyprianou
