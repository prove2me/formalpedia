-- Prove2me | Theorems.Thm_LefebvreVariations_li_coefficient_first_five
-- name    : LefebvreVariations.li_coefficient_first_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:19:29.234873+00:00
-- url     : https://prove2.me/theorems/0cb22d08-0e58-4e96-989e-9565003d1d6d
-- title:
--   Lefebvre's variations, No. 190 — on a theme by Li: the first five Li coefficients are nonnegative
-- statement:
--   Let $\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and, for $m\ge1$,
--   $$
--   \lambda_m=\frac1{(m-1)!}\,\frac{d^m}{ds^m}\Bigl[s^{m-1}\log\xi(s)\Bigr]_{s=1}.
--   $$
--   Then $\lambda_m\ge0$ for $m=1,2,3,4,5$. Numerically $\lambda_1,\dots,\lambda_5=0.023096,\ 0.092346,\ 0.207639,\ 0.368790,\ 0.575543$, and $\lambda_1=1+\gamma/2-\tfrac12\log 4\pi$.
--
--   The parent states $\lambda_m\ge0$ for every $m$, which is Li's criterion, an equivalent of the Riemann hypothesis. Only the first five are claimed here.
--
--   **Formalization Note** As in `BroughanRH.liCoefficient`, $\xi(s)=(1+s(s-1)\Lambda_0(s))/2$ with `completedRiemannZeta₀`, and the index is shifted: the statement quantifies over `n < 5`, taking the real part of `iteratedDeriv (n+1) (s ↦ s^n * log (ξ s)) 1 / n!`, i.e. $\lambda_{n+1}$. The complex logarithm is analytic near $s=1$ since $\xi(1)=1/2>0$, so only a neighbourhood of $1$ matters.
--
--   **Why this is a variation.** Variation on the open platform theorem BroughanRH.liCoefficient (Li's criterion): the parent's own statement for the first five coefficients, which are explicit constants built from Stieltjes-type constants of zeta, and positive by a wide margin.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   X.-J. Li, The positivity of a sequence of numbers and the Riemann hypothesis, J. Number Theory 65 (1997), 325-333 (cited from memory); statement and indexing as on the platform (BroughanRH.liCoefficient). Truth check: lambda_1..lambda_8 computed with mpmath at 40 digits as the Taylor derivatives of s^(m-1) log xi(s) at s = 1: 0.0230957, 0.0923457, 0.2076389, 0.3687905, 0.5755427, 0.8275660, 1.1244601, 1.4657557; lambda_1 agrees with 1 + gamma/2 - log(4 pi)/2 = 0.0230957.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem li_coefficient_first_five :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ n : ℕ, n < 5 →
      0 ≤ ((iteratedDeriv (n+1) (fun s : ℂ => s^n * Complex.log (xi s)) 1) / (n.factorial : ℂ)).re := by
  sorry

end LefebvreVariations
