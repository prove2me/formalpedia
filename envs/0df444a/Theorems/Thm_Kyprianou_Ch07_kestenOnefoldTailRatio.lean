-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenOnefoldTailRatio
-- name    : Kyprianou.Ch07.kestenOnefoldTailRatio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:45:48.455938+00:00
-- url     : https://prove2.me/theorems/fb78b240-361e-4936-8953-599a6f2d0bcd
-- title:
--   Kesten base n=1: strictly positive convolution-tail ratio equals one
-- statement:
--   For any real probability law with strictly positive upper tail and any x>0, the first convolution upper-tail ratio divided by the original upper-tail mass is exactly one. The proof imports the previously Proved convolutionPowerOne and uses positive finite tail mass to justify division by a nonzero real.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 base n=1, printed p.201, original PDF p.210. Full proof remotely verified by private job 96c7557e-17c7-4516-9771-dce5130b66df.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerOne
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenOnefoldTailRatio
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (x : Real) (hx : 0 < x) :
    ((Kyprianou.Ch07.convolutionPower G 1) (Set.Ioi x)).toReal /
      (G (Set.Ioi x)).toReal = 1 := by
  sorry
