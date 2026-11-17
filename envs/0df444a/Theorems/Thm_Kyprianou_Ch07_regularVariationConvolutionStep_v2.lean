-- Prove2me | Theorems.Thm_Kyprianou_Ch07_regularVariationConvolutionStep_v2
-- name    : Kyprianou.Ch07.regularVariationConvolutionStep_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:22:11.693533+00:00
-- url     : https://prove2.me/theorems/50713275-588f-4752-a824-2d79d071ec14
-- title:
--   Lemma 7.13 induction: n-fold asymptotic implies the n+1-fold asymptotic (corrected Lean syntax)
-- statement:
--   For the same normalised heavy-tail law, assume the exact n-fold asymptotic and derive the n+1-fold asymptotic using convolution splitting and middle-region control.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.13 and proof, printed pp. 200–201; original PDF pp. 209–210. Both retain exact parent hypotheses and asymptotic tail conclusion for their stage. Parent UUID bcd7e478-c3c2-45c6-a0d8-590e5e62cdb8. Repaired publication candidate after the earlier source generator emitted a malformed Lean let-expression and unparenthesised convolutionPower application; no mathematical target change.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.regularVariationConvolutionStep_v2
    (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hPositiveJumpSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    let nu : Measure Real := largeJumpNormalisedLaw PiH;
    ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower nu n) (Set.Ioi x)).toReal /
          (((n : Nat) : Real) * (nu (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)) →
      Tendsto (fun x : Real =>
        ((convolutionPower nu (n + 1)) (Set.Ioi x)).toReal /
          (((n + 1 : Nat) : Real) * (nu (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)) := by
  sorry
