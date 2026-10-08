-- Prove2me | Theorems.Thm_NesterovRCD_Accelerated_ab_growth
-- name    : NesterovRCD.Accelerated.ab_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:21.92406+00:00
-- url     : https://prove2.me/theorems/3a882b50-87f4-4ce7-8409-ca4a513b1803
-- title:
--   Proof of Theorem 6, p. 17 — $a_k\ge\frac1{\sqrt\sigma}[Q_1^{k+1}-Q_2^{k+1}]$, $b_k\ge Q_1^{k+1}+Q_2^{k+1}$
-- statement:
--   Let $n\ge1$ and $0<\sigma<n^2$, let $a_k,b_k$ be the coefficients of the method ACDM$(x_0)$ (5.1), and put
--   $$Q_1=1+\frac{\sqrt\sigma}{2n},\qquad Q_2=1-\frac{\sqrt\sigma}{2n}.$$
--   Then for every $k\ge0$
--   $$a_k\ge\frac1{\sqrt\sigma}\Big[Q_1^{k+1}-Q_2^{k+1}\Big],\qquad b_k\ge Q_1^{k+1}+Q_2^{k+1}.$$
--
--   This lower bound on $a_k$ converts the potential inequality of the proof of Theorem 6 into the first, linear-rate bound of (5.3).
--
--   **Formalization Note** The paper does not restrict $\sigma$ here, but divides by $\sqrt\sigma$; the statement assumes $\sigma>0$ (at $\sigma=0$ Lean's $1/0=0$ would make the bound on $a_k$ trivial). The hypothesis $\sigma<n^2$ is implicit in (5.1).
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 17, proof of Theorem 6, after (5.5)

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Accelerated_ACDM

namespace NesterovRCD.Accelerated

theorem ab_growth (n : ℕ) (hn : 0 < n) (σ : ℝ) (hσ : 0 < σ) (hσn : σ < (n : ℝ) ^ 2) (k : ℕ) :
    1 / Real.sqrt σ * ((1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1))
      ≤ acdmA n σ k ∧
    (1 + Real.sqrt σ / (2 * n)) ^ (k + 1) + (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)
      ≤ acdmB n σ k := by sorry

end NesterovRCD.Accelerated
