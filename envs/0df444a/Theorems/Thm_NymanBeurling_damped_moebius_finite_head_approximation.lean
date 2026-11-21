-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_finite_head_approximation
-- name    : NymanBeurling.damped_moebius_finite_head_approximation
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T01:10:51.826766+00:00
-- url     : https://prove2.me/theorems/4a378c4e-7531-46cc-ac6f-75ab33d717a6
-- title:
--   Unconditional finite-coordinate approximation by damped Mobius remainder sums
-- statement:
--   For $N\ge0$, $\varepsilon>0$ and $m\ge1$, write
--   $$E_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\frac{\mu(d)}{d^\varepsilon}\frac{m\bmod d}{d}.$$
--   For every finite coordinate cutoff $H\ge0$ and every $\delta>0$, there is $\varepsilon_0>0$ such that, for every $0<\varepsilon<\varepsilon_0$, there is $N_0$ for which every $N\ge N_0$ satisfies
--   $$\sum_{m=1}^{H}\frac{E_{N,\varepsilon}(m)^2}{m(m+1)}<\delta.$$
--   This theorem is unconditional. The coordinate cutoff $H$ is fixed before the damping threshold is chosen, and $N_0$ may depend on $\varepsilon$. It establishes the finite-coordinate component of the damped approximation frontier. It does not assert a bound uniform in $H$, or a truncation threshold uniform as $\varepsilon$ tends to zero.
-- source:
--   Derived unconditional finite-coordinate lemma for https://prove2.me/theorems/cf53c71e-758a-4724-897b-66cd8091e51b . The only platform theorem used is the proved Abel limit https://prove2.me/theorems/ba6f3ccb-a3be-4de1-87b4-4fce40840ec3 . The divisor identity and absolutely convergent Dirichlet series are handled using Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474. The weighted remainder sequence model is from B. Bagchi (2006), Theorem 1, https://arxiv.org/pdf/math/0607733 ; the present explicit iterated finite-coordinate quantifiers are a derived statement, not a quotation.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.damped_moebius_finite_head_approximation (H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∑ n ∈ Finset.range H,
          (1 + ∑ k : Fin N,
            ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
              (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by sorry
