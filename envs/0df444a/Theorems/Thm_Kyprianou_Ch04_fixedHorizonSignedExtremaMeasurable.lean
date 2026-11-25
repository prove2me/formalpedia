-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaMeasurable
-- name    : Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T12:42:48.417894+00:00
-- url     : https://prove2.me/theorems/9a73a587-4df0-59fc-b1c7-b727947f1181
-- title:
--   Deterministic-time signed drawdown and running infimum are measurable
-- statement:
--   Use joint measurability of the two extrema and the endpoint, with the compact-interval supremum representation.
-- source:
--   Kyprianou (2006), Corollary 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) :
    Measurable (fun w : Ω => L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t)) ∧
    Measurable (fun w : Ω => sInf ((fun s : NNReal => L.X s w) '' Iic t)) := by
  sorry
