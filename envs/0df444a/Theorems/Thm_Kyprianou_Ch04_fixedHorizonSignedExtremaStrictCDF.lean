-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaStrictCDF
-- name    : Kyprianou.Ch04.fixedHorizonSignedExtremaStrictCDF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:43:00.678422+00:00
-- url     : https://prove2.me/theorems/a6c4c178-1292-471f-814a-680b1bcf112a
-- title:
--   Fixed-horizon strict lower rays agree by time reversal
-- statement:
--   Identify strict lower rays via bounded compact path extrema and apply the proved fixed-horizon strict reversal.
-- source:
--   Kyprianou (2006), Corollary 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.fixedHorizonSignedExtremaStrictCDF
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ht : 0 < t) (a : ℝ) :
    P {w : Ω | L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t) < a} =
      P {w : Ω | sInf ((fun s : NNReal => L.X s w) '' Iic t) < a} := by
  sorry
