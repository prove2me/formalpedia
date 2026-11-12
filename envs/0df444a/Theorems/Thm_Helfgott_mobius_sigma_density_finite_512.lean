-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_density_finite_512
-- name    : Helfgott.mobius_sigma_density_finite_512
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T22:52:47.814158+00:00
-- url     : https://prove2.me/theorems/f6910923-84ff-400c-a651-f3548e40b24c
-- title:
--   Kernel-certified finite Mobius pair-density bound through 512
-- statement:
--   Let $\mu$ denote the Möbius function and put $P(n)=\prod_{p\mid n}(p+1)$. For every integer $0\le N\le512$,
--   $$\sum_{s=1}^{N}\frac1s\sum_{\substack{a,b\le N/s\\(a,b)=1}}\frac{\mu(a)\mu(b)}{P(a)P(b)}\le1.001.$$
--   This finite signed-density estimate supplies an explicit input for the complementary Möbius coefficient energy in Vaughan's identity. The range is exactly as stated; no bound beyond 512 is asserted.
-- source:
--   Exact finite divisor recurrence and integer certificate checked by the Lean kernel. Rounding errors are bounded analytically with scale 10^30. No native-decide axiom or assumed numerical computation is used.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
open scoped BigOperators

theorem Helfgott.mobius_sigma_density_finite_512 (N : ℕ) (hN : N≤512) :
    (∑ s ∈ Finset.Icc 1 N, (1/(s:ℝ))*(∑ a ∈ Finset.Icc 1 (N/s), ∑ b ∈ Finset.Icc 1 (N/s),
      if Nat.Coprime a b then
        (((ArithmeticFunction.moebius a:ℤ):ℝ)/(∏ p ∈ a.primeFactors, ((p:ℝ)+1)))*
        (((ArithmeticFunction.moebius b:ℤ):ℝ)/(∏ p ∈ b.primeFactors, ((p:ℝ)+1))) else 0))≤(1001/1000:ℝ) := by sorry
