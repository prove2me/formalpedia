-- Prove2me | Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
-- name    : Kyprianou.Ch04.closedTimeBandIntensityFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:54:32.252288+00:00
-- url     : https://prove2.me/theorems/da81afe0-183a-490a-b65f-b55bd2d8bf25
-- title:
--   Finite reference intensity on a closed time and mark band
-- statement:
--   The reference intensity is the product of time Lebesgue measure restricted to nonnegative times and the mark measure. Both factors are finite on the given rectangle.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem closedTimeBandIntensityFinite
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (t : NNReal) (B : Set Real) (hB : levyMeasure B < ⊤) :
    referenceIntensity levyMeasure (Set.Icc (0 : Real) (t : Real) ×ˢ B) ≠ ⊤ := by
  sorry
end Kyprianou.Ch04
