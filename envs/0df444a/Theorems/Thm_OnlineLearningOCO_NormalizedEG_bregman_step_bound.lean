-- Prove2me | Theorems.Thm_OnlineLearningOCO_NormalizedEG_bregman_step_bound
-- name    : OnlineLearningOCO.NormalizedEG.bregman_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:07.044755+00:00
-- url     : https://prove2.me/theorems/5e2c62c6-f2a3-4317-865d-651787fdd017
-- title:
--   Proof of Theorem 2.22 — D_{R⋆}(−z_{1:t} ‖ −z_{1:t−1}) ≤ η Σᵢ wₜ[i]zₜ[i]² when ηzₜ[i] ≥ −1
-- statement:
--   Let $d \ge 1$, $\eta > 0$, let $z_1, z_2, \dots \in \mathbb R^d$ be loss vectors, let $w_t$ be the normalized-EG weights $w_t[i] = e^{-\eta z_{1:t-1}[i]} / \sum_j e^{-\eta z_{1:t-1}[j]}$, and let $R^\star(\theta) = \frac1\eta\log\big(\sum_i e^{\eta\theta[i]}\big)$. If at round $t$ we have $\eta z_t[i] \ge -1$ for every $i$, then
--   $$D_{R^\star}(-z_{1:t}\,\|\,-z_{1:t-1}) \le \eta \sum_{i} w_t[i]\, z_t[i]^2 .$$
--
--   This is the per-round bound that, summed over $t$ and combined with Lemma 2.20, gives the local-norm regret bound of Theorem 2.22. The right-hand side is $\eta\|z_t\|_t^2$ for the local norm $\|z\|_t = \sqrt{\sum_i w_t[i] z[i]^2}$ (p. 153).
--
--   **Formalization Note** Rounds are numbered from $0$: `wmWeights η z t` is the paper's $w_{t+1}$, and `cumSum z t` is the paper's $z_{1:t}$. The Bregman divergence is that of $R^\star$ with the softmax as its gradient (`bregmanLSE`).
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, pp. 153–154, §2.8, proof of Theorem 2.22 (claim on p. 153, last display on p. 154)

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
import Definitions.Def_UnderstandingML_Online

namespace OnlineLearningOCO.NormalizedEG

open UnderstandingML

/-- §2.8, proof of Theorem 2.22, pp. 153–154. If `η > 0` and `η z_t[i] ≥ −1` for every `i`, the
Bregman divergence of the log-sum-exp conjugate `R⋆(θ) = (1/η) log ∑_i e^{η θ[i]}` along the
normalized-EG run is bounded by the local norm of `z_t`:
`D_{R⋆}(−z_{1:t} ‖ −z_{1:t−1}) ≤ η ∑_i w_t[i] z_t[i]²`.
Rounds are 0-based: `wmWeights η z t` is the paper's `w_{t+1}`. -/
theorem bregman_step_bound {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 < η) (z : ℕ → Fin d → ℝ) (t : ℕ)
    (hz : ∀ i, -1 ≤ η * z t i) :
    bregmanLSE η (-(cumSum z (t + 1))) (-(cumSum z t)) ≤
      η * ∑ i, wmWeights η z t i * z t i ^ 2 := by sorry

end OnlineLearningOCO.NormalizedEG
