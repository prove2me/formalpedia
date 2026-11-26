-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clockSignedInfimumLaw
-- name    : Kyprianou.Ch04.clockSignedInfimumLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:44:26.253772+00:00
-- url     : https://prove2.me/theorems/a5edf813-1b8e-4b2c-a95c-f873e3c31391
-- title:
--   Signed product-clock drawdown and infimum law
-- statement:
--   Negate the two identically distributed clock extrema and identify the range representation of the actual running infimum.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.clockSignedInfimumLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (q : ℝ) (hq : 0 < q) :
    IdentDistrib
      (fun z : Ω × ℝ => -(runningSup L z.2.toNNReal z.1 - L.X z.2.toNNReal z.1))
      (fun z : Ω × ℝ => sInf ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal))
      (P.prod (expMeasure q)) (P.prod (expMeasure q)) := by
  sorry
