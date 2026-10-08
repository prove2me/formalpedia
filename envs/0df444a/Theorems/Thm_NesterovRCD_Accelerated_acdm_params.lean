-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_acdm_params
-- name    : NesterovRCD.Accelerated.acdm_params
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:10.388214+00:00
-- url     : https://prove2.me/theorems/e0222d83-67ae-41a8-af79-6be89af898a0
-- title:
--   (5.1), step 1 — ACDM is well defined: $\gamma_k\ge1/n$ is the unique such root, $0<\alpha_k,\beta_k\le1$, $a_k,b_k>0$
-- statement:
--   Let $n\ge1$ and $0\le\sigma<n^2$, and let $a_k,b_k,\gamma_k,\alpha_k,\beta_k$ be the coefficients of the method ACDM$(x_0)$ (5.1). Then for every $k\ge0$:
--
--   1. $a_k>0$ and $b_k>0$;
--   2. $\gamma_k\ge\frac1n$ and $\gamma_k$ solves the equation of step 1,
--   $$\gamma_k^2-\frac{\gamma_k}{n}=\Big(1-\frac{\gamma_k\sigma}{n}\Big)\frac{a_k^2}{b_k^2};$$
--   3. it is the only solution $\gamma\ge\frac1n$ of this equation;
--   4. $0<\alpha_k\le1$ and $0<\beta_k\le1$.
--
--   Step 1 of (5.1) instructs to "compute $\gamma_k\ge\frac1n$ from equation …" and then divides by $\gamma_k(n^2-\sigma)$ and by $\sqrt{\beta_k}$. This statement certifies that the instruction determines $\gamma_k$, that the encoded closed form is that root, and that the subsequent steps are well defined: $y_k$ is a convex combination of $v_k$ and $x_k$, and $\beta_k v_k+(1-\beta_k)y_k$ is a convex combination of $v_k$ and $y_k$.
--
--   **Formalization Note** These facts are implicit in the paper (not printed claims). The hypothesis $\sigma<n^2$ is implicit in the paper: $\alpha_k$ divides by $n^2-\sigma$. With footnote 2 of p. 14 ($\sigma\le1$ under (2.2)) it excludes only the case $n=1$, $\sigma=1$, in which $\alpha_k$ is undefined.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 15, Method ACDM(x_0), (5.1), steps 1 and 4 (well-definedness; not a printed claim)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem acdm_params (n : ℕ) (hn : 0 < n) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (k : ℕ) :
    0 < acdmA n σ k ∧ 0 < acdmB n σ k ∧
    1 / (n : ℝ) ≤ acdmGamma n σ k ∧
    acdmGamma n σ k ^ 2 - acdmGamma n σ k / n
      = (1 - acdmGamma n σ k * σ / n) * (acdmA n σ k ^ 2 / acdmB n σ k ^ 2) ∧
    (∀ g : ℝ, 1 / (n : ℝ) ≤ g →
      g ^ 2 - g / n = (1 - g * σ / n) * (acdmA n σ k ^ 2 / acdmB n σ k ^ 2) →
      g = acdmGamma n σ k) ∧
    0 < acdmAlpha n σ k ∧ acdmAlpha n σ k ≤ 1 ∧
    0 < acdmBeta n σ k ∧ acdmBeta n σ k ≤ 1 := by sorry

end NesterovRCD.Accelerated
