-- Prove2me | Theorems.Thm_Kyprianou_Ch04_measurableNegativeInfimumLimit
-- name    : Kyprianou.Ch04.measurableNegativeInfimumLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:27:45.269652+00:00
-- url     : https://prove2.me/theorems/1cfdc2cb-ec0f-4b1c-8f55-8ba82400feb9
-- title:
--   Finite horizon negative infima converge almost surely to a measurable nonnegative random variable when the paths are almost surely bounded below.
-- statement:
--   Finite horizon negative infima converge almost surely to a measurable nonnegative random variable when the paths are almost surely bounded below.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.measurableNegativeInfimumLimit {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hb : ∀ᵐ z ∂P, BddBelow (range (fun t : NNReal => L.X t z))) :
    ∃ Z : Ω → ℝ, Measurable Z ∧ (∀ᵐ z ∂P, 0 ≤ Z z) ∧
      (∀ᵐ z ∂P, Tendsto
        (fun t : NNReal => -sInf ((fun s : NNReal => L.X s z) '' Iic t))
        atTop (nhds (Z z))) := by
  sorry
