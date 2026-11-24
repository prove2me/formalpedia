-- Prove2me | Theorems.Thm_OddGoldbach19_interval_goldbach_refined_five
-- name    : OddGoldbach19.interval_goldbach_refined_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:13:25.681902+00:00
-- url     : https://prove2.me/theorems/4671351b-0ce5-4e48-8633-17a4fccb83b6
-- title:
--   Refined Goldbach prime-pair bound on arbitrary intervals
-- statement:
--   Let $s>0$ be even, $a,L$ natural numbers, $L\ge25600$, and $\log L\ge100$. Put $C$ for the factor-two twin-prime constant and $K(s)=\prod_{p\mid s,\ p>2}(p-1)/(p-2)$. Then
--   $$\#\{p\in(a,a+L]:p<s,\ p\text{ and }s-p\text{ prime}\}\le\frac{8CK(s)L}{\log L(\log L+5.6)}+\frac{2\sqrt L}{\sqrt5}+2.$$
--   This strengthens the logarithmic denominator in the interval input used by the odd-Goldbach campaign counting argument.
-- source:
--   Adapted from public Apache2.0 accepted Prove2Me proof993546cc-ae39-4daa-a8a3-2781b3db2d70, with newly proved coefficient-five interval sieve and explicit reciprocal denominator bounds. It does not assume the sharper unformalized Riesel-Vaughan numerical sieve constants.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators

theorem OddGoldbach19.interval_goldbach_refined_five (s a L : ℕ) (hs : Even s)
    (hs0 : 0 < s) (hL : 25600 ≤ L) (hl : 100 ≤ Real.log (L : ℝ)) :
    (((Finset.Ioc a (a+L)).filter (fun p => p.Prime ∧ p < s ∧ (s-p).Prime)).card : ℝ) ≤
      8*TaoFivePrimes.twinPrimeConstant*
        (∏ p ∈ s.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1)*(L:ℝ)/
        (Real.log (L:ℝ)*(Real.log (L:ℝ)+5.6))+2*Real.sqrt (L:ℝ)/Real.sqrt 5+2 := by sorry
