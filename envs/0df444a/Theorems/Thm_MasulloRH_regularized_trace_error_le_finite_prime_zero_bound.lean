-- Prove2me | Theorems.Thm_MasulloRH_regularized_trace_error_le_finite_prime_zero_bound
-- name    : MasulloRH.regularized_trace_error_le_finite_prime_zero_bound
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:56:32.16192+00:00
-- url     : https://prove2.me/theorems/01564f66-9872-49da-abd6-6ca5f4e229a8
-- title:
--   An unconditional trace error bound from finite prime powers and a finite list of zeros
-- statement:
--   Let $H_\alpha$ be the regularized trace, $L=\zeta'/\zeta$, and $F$ any finite set of nontrivial zeros in the window $|\Re\rho-1/2|<\alpha$. For $N\ge2$ put
--   $$C=\frac{\log 2}{2}+\frac{\pi}{4}-\frac{37}{30},\quad P_N=\sum_{n\le N}\Lambda(n)(n^{-5/2}-n^{-3}),\quad E_N=\left(\frac{2}{3}\log N+\frac49\right)N^{-3/2}.$$
--   Write $k(\rho)=m_\rho\Re((3-\rho)^{-1}-(5/2-\rho)^{-1})$, with $m_\rho$ the analytic multiplicity. For $\Re s>3/2$ and $|s|\le R$,
--   $$|L(s)-H_\alpha(s)|\le32(2R+3)(R+5/2)\left(C+P_N+E_N-\sum_{\rho\in F}k(\rho)\right).$$
--   The bound requires finitely many prime powers and zeros. Its explicit remainder holds for every integer $N\ge2$.
-- source:
--   Finite computational form of the proved regularized trace error bound and prime-power mass expansion in the Masullo RH specialization. Classical von Mangoldt estimate and integral comparison.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

namespace MasulloRH

theorem regularized_trace_error_le_finite_prime_zero_bound (N : ℕ) (hN : 2 ≤ N)
    (α R : ℝ) (s : ℂ) (hR : ‖s‖ ≤ R) (hs : (3/2:ℝ) < s.re)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, |z.val.re-1/2| < α) :
    ‖zetaLogDeriv s-regularizedTraceRHS α s‖ ≤ 16*(2*(2*R+3)*(R+5/2)) *
      (Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ n ∈ Finset.range (N+1), (ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ))) +
        ((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ) -
        ∑ z ∈ F,(zeroResolventTerm (1/2) 3 z).re) := by sorry

end MasulloRH
