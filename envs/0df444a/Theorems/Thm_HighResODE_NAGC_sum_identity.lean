-- Prove2me | Theorems.Thm_HighResODE_NAGC_sum_identity
-- name    : HighResODE.NAGC.sum_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:14.735917+00:00
-- url     : https://prove2.me/theorems/37f14970-6b69-47a1-8910-bdf965e106b5
-- title:
--   Proof of Theorem 6, sum identity, p. 26 — Σ_{i=3}^{k−1}[(i + 3)(i − 1) − (i + 3)(i + 1)/3] = (2k³ − 38k + 60)/9 ≥ (k + 1)³/36
-- statement:
--   For every integer $k\ge4$,
--   $$
--   \sum_{i=3}^{k-1}\Bigl[(i+3)(i-1)-\frac13(i+3)(i+1)\Bigr]=\frac{2k^3-38k+60}{9}\ge\frac{(k+1)^3}{36}.
--   $$
--
--   The sum is the total weight that the telescoped Lemma 4.3 places on the squared gradient norms $\|\nabla f(x_4)\|^2,\dots,\|\nabla f(x_k)\|^2$ at the largest step size $s=1/(3L)$; its cubic growth gives the $k^{-3}$ rate.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 26, proof of Theorem 6 (display following (4.9))

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- Proof of Theorem 6, sum identity, p. 26. -/
theorem sum_identity (k : ℕ) (hk : 4 ≤ k) :
    ∑ i ∈ Finset.Ico 3 k,
        (((i : ℝ) + 3) * ((i : ℝ) - 1) - 1 / 3 * ((i : ℝ) + 3) * ((i : ℝ) + 1))
      = (2 * (k : ℝ) ^ 3 - 38 * (k : ℝ) + 60) / 9 ∧
    ((k : ℝ) + 1) ^ 3 / 36 ≤ (2 * (k : ℝ) ^ 3 - 38 * (k : ℝ) + 60) / 9 := by sorry

end HighResODE.NAGC
