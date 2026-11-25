-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaLaplaceEquality
-- name    : Kyprianou.Ch04.fixedHorizonSignedExtremaLaplaceEquality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:46:41.661247+00:00
-- url     : https://prove2.me/theorems/84705e4c-e547-401c-bd88-bbf5fd0dd184
-- title:
--   Fixed-horizon reflected drawdown and running infimum have identical exponential transforms
-- statement:
--   For any strictly positive deterministic horizon on the original Levy probability space, the fixed-horizon reflection-duality result implies equality of the exponential expectations of signed drawdown and running infimum. No new moment assumptions are needed for IdentDistrib integral_eq.
-- source:
--   Kyprianou (2006), Corollary 4.9 p100 via distributional duality, following Theorem 4.8.

import Mathlib
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.fixedHorizonSignedExtremaLaplaceEquality
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) (ht : 0 < t)
    (beta : ℝ) :
    (∫ w : Ω, Real.exp (beta *
      (L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t))) ∂P) =
    (∫ w : Ω, Real.exp (beta *
      (sInf ((fun s : NNReal => L.X s w) '' Iic t))) ∂P) := by
  sorry
