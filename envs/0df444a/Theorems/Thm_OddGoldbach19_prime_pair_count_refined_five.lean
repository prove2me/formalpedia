-- Prove2me | Theorems.Thm_OddGoldbach19_prime_pair_count_refined_five
-- name    : OddGoldbach19.prime_pair_count_refined_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:19:13.410258+00:00
-- url     : https://prove2.me/theorems/dc7b6185-80ab-45b8-82b3-9bd5ad7639be
-- title:
--   Prime-pair upper bounds with positive logarithmic denominator shifts
-- statement:
--   Let $x,d$ be natural numbers, $x\ge5$, and $d>0$ even. Write $C$ for the factor-two twin-prime constant and $K(d)=\prod_{p\mid d,\ p>2}(p-1)/(p-2)$. If $\log x\ge40$, then
--   $$\#\{n:n,n+d\text{ prime},\ n+d\le x\}\le\frac{8CK(d)x}{\log x(\log x+4)}.$$
--   For $\log x\ge100$, the same bound holds with $5.5$ in place of $4$. These explicit improvements provide the off-diagonal input for the campaign's finite-shift second moment argument.
-- source:
--   New consequence of the proved coefficient-five prime-pair reciprocal bound and explicit denominator-five comparisons. The additive cutoff error is absorbed by an elementary exponential Taylor lower bound. These constants are derived from the specified platform inputs and do not assert the stronger source-paper constants.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators

theorem OddGoldbach19.prime_pair_count_refined_five (x d : ℕ) (hx : 5≤x)
    (hd0 : 0<d) (hd : 2∣d) (hl : 40≤Real.log (x:ℝ)) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d≤x then (1:ℝ) else 0) ≤
    8*TaoFivePrimes.twinPrimeConstant*
      (∏ p ∈ d.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1)*(x:ℝ)/
        (Real.log (x:ℝ)*(Real.log (x:ℝ)+4)) ∧
    (100≤Real.log (x:ℝ) →
      (∑ n ∈ Finset.range (x+1),
        if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d≤x then (1:ℝ) else 0) ≤
      8*TaoFivePrimes.twinPrimeConstant*
        (∏ p ∈ d.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1)*(x:ℝ)/
          (Real.log (x:ℝ)*(Real.log (x:ℝ)+5.5))) := by sorry
