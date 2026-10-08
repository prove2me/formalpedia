-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_eq_5_4
-- name    : NesterovRCD.Accelerated.eq_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:02.954814+00:00
-- url     : https://prove2.me/theorems/d347140c-8aec-49b1-a630-f6733784985b
-- title:
--   (5.4) — $b_{k+1}\ge b_k+\frac{\sigma}{2n}a_k$
-- statement:
--   Let $n\ge1$ and $0\le\sigma<n^2$, and let $a_k,b_k$ be the coefficients of the method ACDM$(x_0)$ (5.1). Then for every $k\ge0$
--   $$\frac{\sigma}{n}a_{k+1}b_{k+1}\le b_{k+1}^2-b_k^2\le 2b_{k+1}(b_{k+1}-b_k),$$
--   and therefore
--   $$b_{k+1}\ge b_k+\frac{\sigma}{2n}a_k.$$
--
--   Together with (5.5) this recursion drives the growth of $a_k$ and $b_k$ that yields the rate of Theorem 6.
--
--   **Formalization Note** The hypothesis $\sigma<n^2$ is implicit in the paper: $\alpha_k$ divides by $n^2-\sigma$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 16, proof of Theorem 6, (5.4)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem eq_5_4 (n : ℕ) (hn : 0 < n) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσn : σ < (n : ℝ) ^ 2) (k : ℕ) :
    σ / n * acdmA n σ (k + 1) * acdmB n σ (k + 1) ≤ acdmB n σ (k + 1) ^ 2 - acdmB n σ k ^ 2 ∧
    acdmB n σ (k + 1) ^ 2 - acdmB n σ k ^ 2
      ≤ 2 * acdmB n σ (k + 1) * (acdmB n σ (k + 1) - acdmB n σ k) ∧
    acdmB n σ k + σ / (2 * n) * acdmA n σ k ≤ acdmB n σ (k + 1) := by sorry

end NesterovRCD.Accelerated
