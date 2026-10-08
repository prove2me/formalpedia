-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_single_log_polynomial_saving
-- name    : OAI.TwoPointCorrelations.halasz_single_log_polynomial_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:47.74016+00:00
-- url     : https://prove2.me/theorems/31e395b9-227a-4974-a34e-8b0496438e40
-- title:
--   Vinogradov-type saving for the degree-k Taylor polynomial of t·log(z+b) at one scale d
-- statement:
--   There is $R_0\in\mathbb N$ such that for all naturals $k\ge2$, $M\ge1$, $1\le d\le k$, and reals $t,z,N,\lambda,q$ with $M\le N\le z\le2N$, $|t|=N^\lambda$, $N^{1/3}\le2M$ and $q+k^2/1024\le\min\big(\frac d3,\ d-\lambda,\ \lambda-\frac d3\big)$,
--
--   $$\frac1{M^2}\Big|\sum_{b=1}^MV_{k,M}\big((\gamma_jb^j)_{j=1}^k\big)\Big|\le(R_0+k+32)^6\,N^{-q/(2m_k^2)},$$
--
--   where $V_{k,M}(\alpha)=\sum_{n=1}^Me(\sum_jn^j\alpha_j)$, $\gamma_j=\frac{t(-1)^{j-1}}{2\pi jz^j}$ (`halaszLogCoefficient t z`), the products are taken modulo $1$, and $m_k=(10k+1)k$ (`halaszSelectedMoment k`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_single_log_polynomial_saving`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem halasz_single_log_polynomial_saving : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤ k →
    ∀ M : ℕ, 1≤ M → ∀ d : ℕ, 1≤ d → d≤ k → ∀ t z N lam q : ℝ,
    (M:ℝ)≤ N → N≤ z → z≤2*N → |t|=N^lam → N^(1/3:ℝ)≤2*(M:ℝ) →
    q+(k:ℝ)^2/1024≤ min ((d:ℝ)/3) (min ((d:ℝ)-lam) (lam-(d:ℝ)/3)) →
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      (R₀+k+32:ℝ)^6*N^(-q/((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
