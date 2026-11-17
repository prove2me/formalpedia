-- Prove2me | Theorems.Thm_Kyprianou_Ch07_largeJumpNormalisedTailPositive
-- name    : Kyprianou.Ch07.largeJumpNormalisedTailPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:14:48.542874+00:00
-- url     : https://prove2.me/theorems/528b4e57-4fc8-4f5e-87f4-93ac4e2699bd
-- title:
--   Lemma 7.13: normalised large-jump ladder law has strictly positive tails
-- statement:
--   Regular variation of the ascending ladder-height Lévy tail and positive finite mass above one imply strictly positive tails for its normalised large-jump law at every positive level.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.13, normalised large-jump ladder-height law and convolution-tail proof, printed pp. 200–201; original PDF pp. 209–210. Exact full proof source passed private pinned remote Lean compilation.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.largeJumpNormalisedTailPositive
    (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    ∀ x : Real, 0 < x →
      0 < (Kyprianou.Ch07.largeJumpNormalisedLaw PiH) (Set.Ioi x) := by
  sorry
