-- Prove2me | Theorems.Thm_Kyprianou_Ch07_regularVariationConvolutionTwofold_v2
-- name    : Kyprianou.Ch07.regularVariationConvolutionTwofold_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:22:00.760841+00:00
-- url     : https://prove2.me/theorems/2d1edcc2-4b6e-4cc7-b3fc-b4a07c8b6ecc
-- title:
--   Lemma 7.13 base: the twofold convolution tail is twice the regularly varying tail (corrected Lean syntax)
-- statement:
--   For the normalised large-jump law from a positive-index regularly varying Lévy tail, derive that the twofold convolution has tail ratio two.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.13 and proof, printed pp. 200–201; original PDF pp. 209–210. Both retain exact parent hypotheses and asymptotic tail conclusion for their stage. Parent UUID bcd7e478-c3c2-45c6-a0d8-590e5e62cdb8. Repaired publication candidate after the earlier source generator emitted a malformed Lean let-expression and unparenthesised convolutionPower application; no mathematical target change.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.regularVariationConvolutionTwofold_v2
    (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hPositiveJumpSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    let nu : Measure Real := largeJumpNormalisedLaw PiH;
      Tendsto (fun x : Real =>
        ((convolutionPower nu 2) (Set.Ioi x)).toReal /
          (((2 : Nat) : Real) * (nu (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)) := by
  sorry
