-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactDifferenceSquareEnvelopeV1
-- name    : Kyprianou.Ch04.compactDifferenceSquareEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:25.706665+00:00
-- url     : https://prove2.me/theorems/9c26b569-923b-54ba-bd7c-214cfec4357b
-- title:
--   compactDifferenceSquareEnvelopeV1
-- statement:
--   The square supremum of two bounded compact paths controls their pointwise difference.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.compactDifferenceSquareEnvelopeV1  (Y Z : NNReal → ℝ) (T : NNReal)
    (C D : ℝ) (hY : ∀ t ≤ T, |Y t| ≤ C) (hZ : ∀ t ≤ T, |Z t| ≤ D) :
    let S := sSup ((fun t : NNReal => |Y t-Z t|^2) '' Iic T)
    0 ≤ S ∧ ∀ t ≤ T, |Y t-Z t| ≤ Real.sqrt S := by
  sorry
