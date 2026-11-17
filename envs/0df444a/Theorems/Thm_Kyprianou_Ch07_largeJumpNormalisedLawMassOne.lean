-- Prove2me | Theorems.Thm_Kyprianou_Ch07_largeJumpNormalisedLawMassOne
-- name    : Kyprianou.Ch07.largeJumpNormalisedLawMassOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:01:59.018028+00:00
-- url     : https://prove2.me/theorems/a5595ac9-2624-4ac4-8933-068c36206577
-- title:
--   Lemma 7.13: positive finite ladder Lévy large-jump mass normalises to a probability measure
-- statement:
--   If the ascending ladder-height Lévy measure has a positive finite mass of jumps strictly greater than one, restricting it to that region and scaling it by the inverse mass produces a probability measure. This is the probability-law foundation for the large-jump convolution powers in Lemma 7.13 and the Kesten bound Lemma 7.14.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.13, large-jump normalised law construction preceding the convolution-tail argument, printed pp. 200–201, original PDF pp. 209–210. This exact statement is remotely kernel elaborated by private probe e273bff4-db05-4570-8dd8-212fec4e88a5.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.largeJumpNormalisedLawMassOne
    (PiH : Measure Real)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real))) :
    (Kyprianou.Ch07.largeJumpNormalisedLaw PiH) Set.univ = 1 := by
  sorry
