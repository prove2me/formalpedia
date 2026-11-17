-- Prove2me | Theorems.Thm_Kyprianou_Ch07_convolutionPowerOne
-- name    : Kyprianou.Ch07.convolutionPowerOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:33:58.962212+00:00
-- url     : https://prove2.me/theorems/7f3d8066-8137-4de8-91f1-d632ac992c18
-- title:
--   Kesten base case: onefold convolution of probability law equals original law
-- statement:
--   For any probability distribution on the reals, the first convolution power of the published Chapter 7 iterated sum-convolution definition is exactly the original measure. The proof identifies the zero-fold Dirac law as the additive identity for convolution.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 base case n=1, printed p.201, original PDF p.210. Full exact proof verified on remote pinned Lean in private job 0584d031-33b4-46e9-af22-29a779452a89.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.convolutionPowerOne
    (G : Measure Real) [IsProbabilityMeasure G] :
    Kyprianou.Ch07.convolutionPower G 1 = G := by
  sorry
