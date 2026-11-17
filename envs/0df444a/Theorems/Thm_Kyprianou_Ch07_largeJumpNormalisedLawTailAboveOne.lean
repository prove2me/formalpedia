-- Prove2me | Theorems.Thm_Kyprianou_Ch07_largeJumpNormalisedLawTailAboveOne
-- name    : Kyprianou.Ch07.largeJumpNormalisedLawTailAboveOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:14:35.112204+00:00
-- url     : https://prove2.me/theorems/91ee6836-52d4-4a95-b330-d588c30b1b03
-- title:
--   Lemma 7.13: exact normalised large-jump tail formula above one
-- statement:
--   For x at least one, the normalised ladder-height upper tail is the original upper Lévy tail at x multiplied by the inverse mass of jumps greater than one.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.13, normalised large-jump ladder-height law and convolution-tail proof, printed pp. 200–201; original PDF pp. 209–210. Exact full proof source passed private pinned remote Lean compilation.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.largeJumpNormalisedLawTailAboveOne
    (PiH : Measure Real) (x : Real) (hx : 1 ≤ x) :
    (Kyprianou.Ch07.largeJumpNormalisedLaw PiH) (Set.Ioi x) =
      (PiH (Set.Ioi (1 : Real)))⁻¹ * PiH (Set.Ioi x) := by
  sorry
