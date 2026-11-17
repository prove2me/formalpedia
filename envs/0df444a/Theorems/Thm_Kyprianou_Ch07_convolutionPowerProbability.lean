-- Prove2me | Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
-- name    : Kyprianou.Ch07.convolutionPowerProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:55.704601+00:00
-- url     : https://prove2.me/theorems/98868bad-962c-4da7-829b-a55c38c42824
-- title:
--   Kesten convolution foundation: every convolution power is a probability measure
-- statement:
--   For every probability measure G on the real line, including n=0, every iterated convolutionPower G n is a probability measure. The zero-fold power is the Dirac mass at zero, and the successor is the pushforward of the product of two probability measures under addition.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 and section 7.6, printed p. 201, original PDF p. 210; exact source helper to control upper bounds on n-fold convolution tails. Full source private remote proof job b89c31d8-3c0d-487b-966f-61ec8d00aa30.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.convolutionPowerProbability
    (G : Measure Real) [IsProbabilityMeasure G] (n : Nat) :
    IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) := by
  sorry
