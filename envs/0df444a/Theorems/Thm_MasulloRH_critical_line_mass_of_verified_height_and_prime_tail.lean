-- Prove2me | Theorems.Thm_MasulloRH_critical_line_mass_of_verified_height_and_prime_tail
-- name    : MasulloRH.critical_line_mass_of_verified_height_and_prime_tail
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:12:22.803314+00:00
-- url     : https://prove2.me/theorems/0fdc2a2f-0793-4579-aa93-ba3ccf11b8b8
-- title:
--   A verified zero height and finitely many later prime powers certify one finite trace comparison
-- statement:
--   Put $C=\tfrac12\log2+\tfrac\pi4-\tfrac{37}{30}$, $a(j)=\Lambda(j)(j^{-5/2}-j^{-3})$, and $K(t)=(t^2-5)/(2(t^2+25/4)(t^2+4))$. For an integer $n\ge0$ put $H=5/2+2n$. Let $A$ denote the regularized reference mass, $L=\zeta'/\zeta$, and $U_n=2(8A-\Re L(5/2)+(1+\log n)/2)/(H-1)$, with $\log 0=0$. Suppose all nontrivial zeta zeros through absolute height $H$ have real part $1/2$. Let $N\ge0$ be an integer and $P$ a finite set of integers $p\ge N$ for which $\sum_{p\in P}a(p)\ge U_n$. There is a finite set $F$ of distinct critical-line zeros, counted with analytic multiplicity $m_\rho$, satisfying
--   $$C+\sum_{1\le j<N}a(j)\le\sum_{\rho\in F}m_\rho K(\Im\rho).$$
--   The result certifies a chosen cutoff from a bounded-height zero verification and finite prime-power arithmetic.
-- source:
--   Finite criterion in the Masullo regularized trace reconstruction bd574b97, using the unconditional lattice tail bound 7bc6a754 and the prime expansion c38c09eb. The multiplicity and resolvent comparisons follow Yi’s single-resolvent argument.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

namespace MasulloRH

theorem critical_line_mass_of_verified_height_and_prime_tail (n N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, N ≤ p)
    (hcover : ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ 5/2+2*(n:ℝ) → z.val.re = 1/2)
    (hbudget : 2/((5/2+2*(n:ℝ))-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + (1+Real.log n)/2) ≤
      ∑ p ∈ P, (ArithmeticFunction.vonMangoldt p / (p:ℝ)^(5/2:ℝ) -
        ArithmeticFunction.vonMangoldt p / (p:ℝ)^(3:ℝ))) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
        (∑ j ∈ Finset.range N, (ArithmeticFunction.vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
          ArithmeticFunction.vonMangoldt j / (j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by sorry

end MasulloRH
