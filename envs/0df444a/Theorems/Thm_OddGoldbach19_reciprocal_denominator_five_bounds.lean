-- Prove2me | Theorems.Thm_OddGoldbach19_reciprocal_denominator_five_bounds
-- name    : OddGoldbach19.reciprocal_denominator_five_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:07:24.698497+00:00
-- url     : https://prove2.me/theorems/00a96b9e-24e6-4e9d-ad4e-5a51ae91cad1
-- title:
--   Explicit reciprocal denominator bounds at the coefficient-five cutoff
-- statement:
--   For x>0 with log x>=40, put z=sqrt(x)/sqrt5 and let S(z) be the literal squarefree reciprocal base sum in the statement. Then8*C*S(z)>=log(x)*(log(x)+4.5). If log x>=100, the stronger lower bound with5.6 instead of4.5 holds.
-- source:
--   New explicit consequence of the existing proved reciprocal quadratic expansion, prime second logarithmic moment bound and numerical sieve constants. The lower-constant calculation is adapted from public Apache2.0 accepted proof8679101a-e42f-483f-8760-f50560699bbe. These bounds use the newly justified cutoff sqrt(x)/sqrt5, not the sharper constants quoted in Riesel-Vaughan.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators

theorem OddGoldbach19.reciprocal_denominator_five_bounds (x : ℝ) (hx : 0<x)
    (hl : 40 ≤ Real.log x) :
    Real.log x*(Real.log x+4.5) ≤ 8*TaoFivePrimes.twinPrimeConstant*(∑ n ∈ Finset.Icc 1 ⌊(Real.sqrt x/Real.sqrt 5)⌋₊,
    (if Squarefree n then ∏ p ∈ n.primeFactors,
      if p=2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/(Real.sqrt x/Real.sqrt 5))) ∧
      (100 ≤ Real.log x → Real.log x*(Real.log x+5.6) ≤ 8*TaoFivePrimes.twinPrimeConstant*(∑ n ∈ Finset.Icc 1 ⌊(Real.sqrt x/Real.sqrt 5)⌋₊,
    (if Squarefree n then ∏ p ∈ n.primeFactors,
      if p=2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/(Real.sqrt x/Real.sqrt 5)))) := by sorry
