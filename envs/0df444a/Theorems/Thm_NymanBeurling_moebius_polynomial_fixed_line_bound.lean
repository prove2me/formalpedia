-- Prove2me | Theorems.Thm_NymanBeurling_moebius_polynomial_fixed_line_bound
-- name    : NymanBeurling.moebius_polynomial_fixed_line_bound
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-21T11:40:55.57076+00:00
-- url     : https://prove2.me/theorems/d6f5e94d-d64d-4be3-b952-882091cb75d8
-- title:
--   Uniform Möbius polynomial bound on a fixed vertical line
-- statement:
--   Let $\mu$ denote the Möbius function. For every distance $\eta>0$ from the critical line and every growth exponent $\beta>0$, there is a constant $C\ge0$ such that, for every finite cutoff $N$ and every real ordinate $t$,
--
--   $$
--   \left|\sum_{d=1}^{N}\frac{\mu(d)}{d^{1/2+\eta+it}}\right|\le C(1+|t|)^\beta.
--   $$
--
--   The constant is independent of $N$ and $t$. This fixed-line estimate is the arithmetic input for extending the same bound throughout the half-plane to its right. Bagchi's Lemma 3 gives it under the Riemann hypothesis; the assertion here is an unconditional open problem.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733, p. 140, Lemma 3. The stated fixed-line bound follows from that conditional lemma by taking its half-plane margin smaller than η; removing RH is the explicit open obligation.

import Definitions.Def_NymanBeurling_DampedMellinFrontiers

set_option autoImplicit false

namespace NymanBeurling

theorem moebius_polynomial_fixed_line_bound :
    ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 < β →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (t : ℝ),
        ‖moebiusDirichletPolynomial N (((1 / 2 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (1 + |t|) ^ β := by sorry

end NymanBeurling
