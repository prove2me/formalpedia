-- Prove2me | Theorems.Thm_Kyprianou_Ch07_infinitelyDivisibleRegularlyVaryingTail
-- name    : Kyprianou.Ch07.infinitelyDivisibleRegularlyVaryingTail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:49:53.547993+00:00
-- url     : https://prove2.me/theorems/ff29232b-5a51-4f6f-807f-1781250a5ee0
-- title:
--   Lemma 7.15: infinitely divisible ladder-height tail equivalence
-- statement:
--   Let H be a nonnegative infinitely divisible random variable whose Laplace exponent is dθ+∫_(0,∞)(1−e^(−θx))Π_H(dx), with drift d≥0 and Lévy jump measure Π_H. If Π_H(x,∞) is regularly varying at infinity with index −α for α>0, then P(H>x)∼Π_H(x,∞) as x tends to infinity and the distribution tail of H itself is regularly varying with index −α.
-- source:
--   Kyprianou (2006), first edition, Lemma 7.15 and surrounding Lévy–Khintchine hypotheses in section 7.6, printed p.202, Windows Ky.pdf sheet 106 (original p.211).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Lemma 7.15: the tail of a nonnegative infinitely divisible law
with regularly varying Lévy tail is asymptotic to its Lévy tail,
and the distribution has the same regular variation index. -/
theorem infinitelyDivisibleRegularlyVaryingTail
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (H : Omega → Real)
    (d alpha : Real) (PiH : Measure Real)
    (hHMeasurable : Measurable H)
    (hHNonnegative : ∀ᵐ omega ∂P, 0 ≤ H omega)
    (hD : 0 ≤ d)
    (hAlpha : 0 < alpha)
    (hPiPositiveSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hPiLevy : (∫⁻ x : Real in Set.Ioi 0,
      ENNReal.ofReal (min 1 x) ∂PiH) < ⊤)
    (hLaplace : ∀ theta : Real, 0 ≤ theta →
       (∫ omega, Real.exp (-theta * H omega) ∂P) =
        Real.exp (-(d * theta +
          ∫ x : Real in Set.Ioi (0 : Real),
            (1 - Real.exp (-theta * x)) ∂PiH)))
    (hRegularPi : Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    (Tendsto (fun x : Real =>
       (P {omega | x < H omega}).toReal /
         (PiH (Set.Ioi x)).toReal) atTop (nhds (1 : Real))) ∧
    Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (P {omega | x < H omega}).toReal) (-alpha) := by
  sorry

end Kyprianou.Ch07
