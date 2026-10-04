-- Prove2me | Theorems.Thm_MertensCorrection_prime_correction_tail_half_bound
-- name    : MertensCorrection.prime_correction_tail_half_bound
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-10-03T18:01:48.762981+00:00
-- url     : https://prove2.me/theorems/2f65e746-0478-49ee-95dd-ad36083050ee
-- title:
--   The Mertens correction tail is between zero and 1/(2N)
-- statement:
--   For each prime $p$, set $c(p)=\log(1-1/p)+1/p$. For every integer $N\ge1$, the finite correction and the full correction series satisfy
--
--   $$0\le\sum_{p\le N}c(p)-\sum_p c(p)\le\frac{1}{2N}.$$
--
--   The correction series converges absolutely. The finite sum includes $p=N$ when $N$ is prime, so the omitted tail consists of primes strictly greater than $N$.
--
--   This auxiliary estimate improves the bound $1/N$ used in the existing Mertens correction-tail lemmas. It can reduce the error allowance for a truncated correction series; an explicit Mertens product estimate still requires bounds for the reciprocal-prime sum.
-- source:
--   Elementary proof by logarithm comparison and telescoping. For 0 <= u < 1, -log(1-u)-u <= u^2/(2(1-u)). At u=1/n this is 1/(2(n-1))-1/(2n). Summing over integers n>N bounds the prime tail. Background for the correction-series normalization: R. Vanlalngaia, Explicit Mertens Sums, INTEGERS 17 (2017), A11, equation (17), https://emis.de/ft/19485. No claim is made that the exact 1/(2N) bound is stated in that source.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

theorem MertensCorrection.prime_correction_tail_half_bound (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ∧
    (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (2 * (N : ℝ)) := by sorry
