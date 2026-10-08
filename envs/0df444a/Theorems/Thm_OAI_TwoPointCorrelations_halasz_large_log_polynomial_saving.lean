-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_large_log_polynomial_saving
-- name    : OAI.TwoPointCorrelations.halasz_large_log_polynomial_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:49.356143+00:00
-- url     : https://prove2.me/theorems/781f3a17-efd0-4472-9648-91b29392bffb
-- title:
--   Vinogradov-type saving for the Taylor polynomial of t·log(z+b) in the large-t range
-- statement:
--   There is $R_0\in\mathbb N$ such that for every natural $m\ge8$, natural $M\ge1$, and reals $t,z,N,\lambda$ with $M\le N\le z\le2N$, $|t|=N^\lambda$, $N^{1/4}\le2M$ and $6m-6\le\lambda\le6m$,
--
--   $$\frac1{M^2}\Big|\sum_{b=1}^{M}V_{12m,M}\Big(\big(\gamma_j\,b^{j}\big)_{j=1}^{12m}\Big)\Big|\le(R_0+12m+32)^6\,N^{-1/(10^8\lambda^2)},$$
--
--   where $V_{k,M}(\alpha)=\sum_{n=1}^{M}e\big(\sum_{j=1}^k n^j\alpha_j\big)$ (`halaszVinogradovPolynomial k M`, with $e(x)=e^{2\pi ix}$ on $\mathbb R/\mathbb Z$), and $\gamma_j=\frac{t(-1)^{j-1}}{2\pi jz^j}$ (`halaszLogCoefficient t z`, indexed from $j=1$), the products $\gamma_jb^j$ taken modulo $1$ (`halaszScaledFrequency`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_large_log_polynomial_saving`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem halasz_large_log_polynomial_saving : ∃ R₀ : ℕ, ∀ m : ℕ, 8≤ m →
    ∀ M : ℕ, 1≤ M → ∀ t z N lam : ℝ, (M:ℝ)≤ N → N≤ z → z≤2*N →
    |t|=N^lam → N^(1/4:ℝ)≤2*(M:ℝ) → 6*(m:ℝ)-6≤ lam → lam≤6*m →
    ‖∑ b : Fin M,halaszVinogradovPolynomial (12*m) M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      (R₀+12*m+32:ℝ)^6*N^(-1/((10^8:ℝ)*lam^2)) := by
  sorry

end OAI.TwoPointCorrelations
