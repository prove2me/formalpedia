-- Prove2me | Theorems.Thm_Kyprianou_Ch04_lowerUnboundedFromInfimumZero
-- name    : Kyprianou.Ch04.lowerUnboundedFromInfimumZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:30.178621+00:00
-- url     : https://prove2.me/theorems/67bfddbf-43d2-528c-832b-14ff27135b61
-- title:
--   Vanishing running-infimum transform excludes lower-bounded paths
-- statement:
--   For every fixed integer lower bound, the exponential reward is at least the corresponding strictly positive constant on that event. The threshold estimate and vanishing-expectations lemma imply zero mass of all globally lower-bounded paths.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.lowerUnboundedFromInfimumZero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (hb : 0 < beta)
    (hlim : Tendsto (fun t : NNReal => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P)
      atTop (nhds 0)) :
    P {w | BddBelow (range (fun t : NNReal => L.X t w))} = 0 := by
  sorry
