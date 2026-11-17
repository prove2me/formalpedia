-- Prove2me | Theorems.Thm_Kyprianou_Ch07_regularlyVaryingConvolutionTails
-- name    : Kyprianou.Ch07.regularlyVaryingConvolutionTails
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:48:56.081816+00:00
-- url     : https://prove2.me/theorems/bcd7e478-c3c2-45c6-a0d8-590e5e62cdb8
-- title:
--   Lemma 7.13: asymptotic n-fold convolution tails
-- statement:
--   If the ascending ladder-height Lévy measure Π_H has regularly varying upper tail with index -α for α>0, define ν as Π_H restricted to jumps greater than one and normalised to a probability distribution. Then for every integer n≥2, the n-fold convolution upper tail ν^{*n}(x,∞) is asymptotically equivalent to nν(x,∞) as x tends to infinity. All mass, support and regular-variation conditions make the stated probability law well-defined.
-- source:
--   Kyprianou (2006), Lemma 7.13, printed page 200, Windows Ky.pdf sheet 105 (original single-page PDF p.209).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Lemma 7.13: each fixed convolution power of the normalised
large-jump ladder-height law has an asymptotic tail multiplier n. -/
theorem regularlyVaryingConvolutionTails
    (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hPositiveJumpSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    let nu : Measure Real := largeJumpNormalisedLaw PiH
    ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower nu n) (Set.Ioi x)).toReal /
          ((n : Real) * (nu (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)) := by
  sorry

end Kyprianou.Ch07
