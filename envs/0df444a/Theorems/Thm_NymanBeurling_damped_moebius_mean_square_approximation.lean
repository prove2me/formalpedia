-- Prove2me | Theorems.Thm_NymanBeurling_damped_moebius_mean_square_approximation
-- name    : NymanBeurling.damped_moebius_mean_square_approximation
-- status  : Open
-- author  : @ibecca
-- created : 2026-11-21T00:52:10.31232+00:00
-- url     : https://prove2.me/theorems/cf53c71e-758a-4724-897b-66cd8091e51b
-- title:
--   Uniform weighted approximation by finite damped Mobius remainder sums
-- statement:
--   Write $r_k(m)=(m\bmod(k+2))/(k+2)$ and let $\mu$ be the Möbius function. For every $\delta>0$, the proposed approximation assertion asks for $N\ge0$ and $0<\varepsilon<1/2$ such that, simultaneously for every integer cutoff $H\ge0$,
--
--   $$\sum_{m=1}^{H}\frac{\left(1+\sum_{k=0}^{N-1}\frac{\mu(k+2)}{(k+2)^\varepsilon}r_k(m)\right)^2}{m(m+1)}<\delta.$$
--
--   The coefficients of the approximant to the constant sequence are therefore $b_k=-\mu(k+2)/(k+2)^\varepsilon$. The choice of $N$ and $\varepsilon$ precedes the universal quantifier over $H$; a bound for just one cutoff would not suffice. The terms are nonnegative, so the condition controls the full weighted mean-square error.
--
--   This is an **open unconditional analytic assertion**. Bagchi's construction proves the relevant approximation under the Riemann hypothesis; RH is not an assumption in this formal target, and the paper is not being cited as an unconditional proof. Together with an elementary tail-budget choice and rational rounding, this assertion implies [arbitrarily small finite rational remainder certificates](https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339). It replaces an unrestricted coefficient search by a family with the two parameters $N$ and $\varepsilon$, while retaining the central unresolved analytic difficulty.
-- source:
--   Open unconditional assertion extracted from B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), proof of Theorem 2 (i)=> (ii), pp. 140–141, damped sums H_{L,epsilon}; sign from Mellin identity (4), p. 142, and sequence identification in the proof of Theorem 1, p. 145; https://arxiv.org/pdf/math/0607733 . The source assumes RH in that construction. The present unconditional finite-partial-sum formulation is proposed as an open proof obligation, not as a proved source theorem.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.damped_moebius_mean_square_approximation
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (N : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1/2 ∧ ∀ H : ℕ,
      (∑ n ∈ Finset.range H,
        (1 + ∑ k : Fin N,
          ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
            (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by sorry
