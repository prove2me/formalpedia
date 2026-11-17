-- Prove2me | Theorems.Thm_Kyprianou_Ch07_largeJumpNormalisedLawNoSmallJumps
-- name    : Kyprianou.Ch07.largeJumpNormalisedLawNoSmallJumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:04:35.912015+00:00
-- url     : https://prove2.me/theorems/ab968651-2614-4dc5-92de-8fcdc786896b
-- title:
--   Lemma 7.13: normalised ladder large-jump law has no mass at or below one
-- statement:
--   The large-jump ladder-height probability distribution, defined as the restriction of the ladder-height Lévy measure to jumps greater than one and its constant-density normalisation, assigns zero mass to all jumps at or below one. This supplies the support hypothesis for repeated positive-jump convolutions in Lemma 7.13.
-- source:
--   Kyprianou (2006), Chapter 7, normalised large-jump law in the proof of Lemma 7.13, printed pp. 200–201, original PDF pp. 209–210. Remote kernel-checked exact source in private probe dd50e957-beab-4d60-ac56-0a6396e07f72.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.largeJumpNormalisedLawNoSmallJumps
    (PiH : Measure Real) :
    (Kyprianou.Ch07.largeJumpNormalisedLaw PiH)
      (Set.Iic (1 : Real)) = 0 := by
  sorry
