-- Prove2me | Theorems.Thm_Kyprianou_Ch04_runningInfimumStrictThreshold
-- name    : Kyprianou.Ch04.runningInfimumStrictThreshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:15:52.481596+00:00
-- url     : https://prove2.me/theorems/d4af47c1-2f45-49c7-a417-eb616571d1ed
-- title:
--   Strict running-infimum threshold as existence of an earlier path value
-- statement:
--   A strict inequality above a bounded nonempty infimum is witnessed by a path point; the process starts at zero.
-- source:
--   Kyprianou (2006), Corollary 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.runningInfimumStrictThreshold
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (w : Ω) (a : ℝ) :
    sInf ((fun s : NNReal => L.X s w) '' Iic t) < a ↔
      ∃ s : NNReal, s ≤ t ∧ L.X s w - L.X 0 w < a := by
  sorry
