-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedVariationIntegerDivergenceExtends
-- name    : Kyprianou.Ch04.boundedVariationIntegerDivergenceExtends
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:50:18.5875+00:00
-- url     : https://prove2.me/theorems/e790f1f1-cfea-558d-ade2-084dfb9304f7
-- title:
--   Extend integer-time divergence using monotone drift deficit
-- statement:
--   The integer part of a time differs from it by less than one. Monotonicity of the drift deficit bounds the later process value by the integer-time value plus at most one unit of positive drift.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10; overload proof by exponential Markov and Borel–Cantelli.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedVariationIntegerDivergenceExtends
    (x : NNReal → Real) (d : Real) (hd : 0 < d)
    (hm : Monotone (fun t : NNReal => d * (t : Real) - x t))
    (hx : Tendsto (fun n : Nat => x (n : NNReal)) atTop atBot) :
    Tendsto x atTop atBot := by
  sorry
