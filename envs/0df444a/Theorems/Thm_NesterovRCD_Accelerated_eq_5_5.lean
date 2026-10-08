-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_eq_5_5
-- name    : NesterovRCD.Accelerated.eq_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:25.407992+00:00
-- url     : https://prove2.me/theorems/489ec610-bf88-4bb7-b8f9-067b70463d79
-- title:
--   (5.5) — $a_{k+1}\ge a_k+\frac1{2n}b_k$
-- statement:
--   Let $n\ge1$ and $0\le\sigma<n^2$, and let $a_k,b_k,\beta_k$ be the coefficients of the method ACDM$(x_0)$ (5.1). Then for every $k\ge0$
--   $$\frac{a_{k+1}^2}{b_{k+1}^2}-\frac{a_{k+1}}{nb_{k+1}}=\frac{\beta_ka_k^2}{b_k^2}=\frac{a_k^2}{b_{k+1}^2},$$
--   $$\frac1n a_{k+1}b_{k+1}\le a_{k+1}^2-a_k^2\le 2a_{k+1}(a_{k+1}-a_k),$$
--   and therefore
--   $$a_{k+1}\ge a_k+\frac1{2n}b_k.$$
--
--   Together with (5.4) this recursion drives the growth of $a_k$ and $b_k$ that yields the rate of Theorem 6.
--
--   **Formalization Note** The hypothesis $\sigma<n^2$ is implicit in the paper: $\alpha_k$ divides by $n^2-\sigma$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, pp. 16–17, proof of Theorem 6, (5.5) (display on p. 17)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem eq_5_5 (n : ℕ) (hn : 0 < n) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (k : ℕ) :
    acdmA n σ (k + 1) ^ 2 / acdmB n σ (k + 1) ^ 2 - acdmA n σ (k + 1) / (n * acdmB n σ (k + 1))
      = acdmBeta n σ k * acdmA n σ k ^ 2 / acdmB n σ k ^ 2 ∧
    acdmBeta n σ k * acdmA n σ k ^ 2 / acdmB n σ k ^ 2
      = acdmA n σ k ^ 2 / acdmB n σ (k + 1) ^ 2 ∧
    1 / (n : ℝ) * acdmA n σ (k + 1) * acdmB n σ (k + 1) ≤ acdmA n σ (k + 1) ^ 2 - acdmA n σ k ^ 2 ∧
    acdmA n σ (k + 1) ^ 2 - acdmA n σ k ^ 2
      ≤ 2 * acdmA n σ (k + 1) * (acdmA n σ (k + 1) - acdmA n σ k) ∧
    acdmA n σ k + 1 / (2 * (n : ℝ)) * acdmB n σ k ≤ acdmA n σ (k + 1) := by sorry

end NesterovRCD.Accelerated
