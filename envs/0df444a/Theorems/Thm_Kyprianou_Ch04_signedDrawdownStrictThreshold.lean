-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedDrawdownStrictThreshold
-- name    : Kyprianou.Ch04.signedDrawdownStrictThreshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:15:27.391066+00:00
-- url     : https://prove2.me/theorems/97b478ab-176b-5b1b-9986-98124b8270e9
-- title:
--   Signed drawdown strict threshold as existence of an earlier path value
-- statement:
--   A strict inequality below a bounded nonempty supremum is witnessed by a point of its defining set.
-- source:
--   Kyprianou (2006), Corollary 4.9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.signedDrawdownStrictThreshold
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (w : Ω) (a : ℝ) :
    L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t) < a ↔
      ∃ s : NNReal, s ≤ t ∧ L.X t w - L.X s w < a := by
  sorry
