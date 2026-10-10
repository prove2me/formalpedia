-- Prove2me | Theorems.Thm_HighResODE_NAGC_eq_4_7
-- name    : HighResODE.NAGC.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:32.908483+00:00
-- url     : https://prove2.me/theorems/deed2f2f-2f4e-4e6e-90d6-ccec8a5d26c7
-- title:
--   (4.7)–(4.8), p. 26 — (k + 3)(k − 1) − Ls(k + 3)(k + 1) ≥ 0 for k ≥ 2 when s ≤ 1/(3L)
-- statement:
--   Let $L>0$ and $0<s\le 1/(3L)$. Then for every integer $k\ge2$
--   $$
--   (k+3)(k-1)-Ls(k+3)(k+1)\ge0\qquad\text{and}\qquad s\le\frac1L\cdot\frac{k-1}{k+1}.
--   $$
--
--   This sign condition turns Lemma 4.3 into a monotonicity statement: $\mathcal E(k+1)\le\mathcal E(k)$ for every $k\ge2$.
--
--   **Formalization Note** All quantities are real; $k$ is a natural number cast to $\mathbb R$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 26, (4.7), (4.8), proof of Theorem 6

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

namespace HighResODE.NAGC

open scoped InnerProductSpace

/-- (4.7)–(4.8), proof of Theorem 6, p. 26. -/
theorem eq_4_7 (L s : ℝ) (hL : 0 < L) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L)) (k : ℕ) (hk : 2 ≤ k) :
    0 ≤ ((k : ℝ) + 3) * ((k : ℝ) - 1) - L * s * ((k : ℝ) + 3) * ((k : ℝ) + 1) ∧
    s ≤ 1 / L * (((k : ℝ) - 1) / ((k : ℝ) + 1)) := by sorry

end HighResODE.NAGC
