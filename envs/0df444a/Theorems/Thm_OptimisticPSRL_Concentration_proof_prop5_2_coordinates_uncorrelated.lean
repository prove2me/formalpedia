-- Prove2me | Theorems.Thm_OptimisticPSRL_Concentration_proof_prop5_2_coordinates_uncorrelated
-- name    : OptimisticPSRL.Concentration.proof_prop5_2_coordinates_uncorrelated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:30.534435+00:00
-- url     : https://prove2.me/theorems/5ea8ca69-848f-4ca7-86d8-bd7680f967ac
-- title:
--   Proof of Proposition 5.2, p. 21 — E[Z_{t,i} Z_{t,j}] = 0 for i ≠ j
-- statement:
--   Let $p\in\Delta^S$, $h\in\mathbb R^S$, and let $X$ be one multinoulli trial with parameter $p$. For distinct states $i\ne j$ the coordinates $Z_i(X)$ and $Z_j(X)$ of the proof of Proposition 5.2 are uncorrelated:
--
--   $$
--   \mathbb E\big[Z_i(X)\,Z_j(X)\big]=0.
--   $$
--
--   Together with $\mathbb E[Z_i(X)]=0$ this makes the variance of $Z_t=\sum_iZ_i$ the sum of the variances of its coordinates, which is how the proof identifies the predictable variance.
--
--   **Formalization Note** The paper writes the conditional expectation given $(s_{t-1},a_{t-1})$; in the iid reading of the statement it is the expectation under one draw of law $p$, written as the integral against `cat p`. The text says the coordinates are "independent"; what its display shows and what the proof uses is zero correlation, which is what is stated.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 21, proof of Proposition 5.2, display E[Z_{t,i}Z_{t,j}|s_{t−1},a_{t−1}] = 0

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

namespace OptimisticPSRL.Concentration

open MeasureTheory

/-- Proof of Proposition 5.2 (Agrawal–Jia, arXiv:1705.07041v3, p. 21, the
`E[Z_{t,i}Z_{t,j}|s_{t−1}, a_{t−1}]` display), iid reading: for `i ≠ j`, the coordinates
`Z_i` and `Z_j` of one trial with law `p` have `E[Z_i Z_j] = 0`. -/
theorem proof_prop5_2_coordinates_uncorrelated {S : ℕ} (p h : Fin S → ℝ) (hp : IsProbVec p)
    (i j : Fin S) (hij : i ≠ j) :
    ∫ x, Zcoord p h i x * Zcoord p h j x ∂(cat p) = 0 := by sorry

end OptimisticPSRL.Concentration
