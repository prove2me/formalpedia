-- Prove2me | Theorems.Thm_McFadden1974_MLE_hasGradientAt_L
-- name    : McFadden1974.MLE.hasGradientAt_L
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:03:54.30765+00:00
-- url     : https://prove2.me/theorems/6a19b9af-f7d9-4d5d-8d93-e6c47b6ecb83
-- title:
--   Equation (19) — the gradient of the conditional logit log-likelihood
-- statement:
--   Let $L$ be the conditional logit log-likelihood (18), with selection probabilities $P_{jn}(\theta)$ (16), counts $S_{jn}$ and repetitions $R_n = \sum_j S_{jn} \ge 1$. Then $L$ is differentiable at every $\theta \in \mathbb{R}^K$ and
--   $$\frac{\partial L}{\partial \theta}(\theta) = \sum_{n=1}^N \Big[\sum_{j=1}^{J_n} \big(S_{jn} - R_n P_{jn}(\theta)\big) z_{jn}\Big].$$
--
--   The gradient is the observed minus the expected choice-weighted attribute vectors; it is the first-order condition of maximum likelihood estimation.
--
--   **Formalization Note** The gradient is taken with respect to the Euclidean inner product on $\mathbb{R}^K$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 115 (PDF p. 11), Equation (19)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Equation (19)** (McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 115, PDF p. 11).

The log-likelihood (18) is differentiable at every `θ ∈ ℝ^K`, with gradient
`∂L/∂θ = ∑_{n=1}^N [∑_{j=1}^{J_n} (S_jn − R_n P_jn) z_jn]` (`Data.grad`).

**Formalization Note.** `HasGradientAt` on `EuclideanSpace ℝ (Fin K)` identifies the derivative
with a vector through the Euclidean inner product, which is the paper's `∂L/∂θ`. -/
theorem hasGradientAt_L
    {K : ℕ} (d : Data K) (θ : EuclideanSpace ℝ (Fin K)) :
    HasGradientAt d.L (d.grad θ) θ := by sorry

end McFadden1974.MLE
