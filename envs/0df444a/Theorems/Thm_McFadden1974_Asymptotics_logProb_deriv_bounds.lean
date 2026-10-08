-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_logProb_deriv_bounds
-- name    : McFadden1974.Asymptotics.logProb_deriv_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:12.092169+00:00
-- url     : https://prove2.me/theorems/191564ff-8af8-48dd-bd4f-be7ada9b28a6
-- title:
--   Equation (43) — the first three derivatives of $\log P_{in}$ are bounded by $2M$, $4M^2$, $8M^3$
-- statement:
--   Suppose $|z_{im}| \le M$ for all observations and alternatives (and $J_m \le J_*$). Then for $k = 1, 2, 3$, every observation $m$, alternative $i$ and parameter $\theta$, the $k$-th derivative of $\theta \mapsto \log P_{im}(\theta)$ satisfies
--   $$\bigl\| D^k \log P_{im}(\theta) \bigr\| \le (2M)^k ,$$
--   that is, $|\partial \log P/\partial\theta| \le 2M$, $|\partial^2 \log P/\partial\theta\partial\theta'| \le 4M^2$ and $|\partial^3\log P/\partial\theta\partial\theta'\partial\theta_k| \le 8M^3$, uniformly in $\theta$.
--
--   These uniform bounds control the Taylor expansions of the log-likelihood in the proof of consistency and asymptotic normality.
--
--   **Formalization Note** $D^k$ is the $k$-th Fréchet derivative, a $k$-linear form on $\mathbb R^K$, measured in the operator norm; $z$ and $\theta$ carry the Euclidean norm.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 135, Equation (43) (Lemma 6, proof); PDF p. 31

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Equation (43)** (Lemma 6, proof, p. 135, PDF p. 31): "From Axiom 7, |z_in| ≤ M for a
positive scalar M. Differentiation of Equation (16) yields the bounds
(43) |∂ log P_in/∂θ| ≤ 2M, |∂² log P_in/∂θ∂θ'| ≤ 4M², |∂³ log P_in/∂θ∂θ'∂θ_k| ≤ 8M³,
uniform in θ."

Formalization Note: the `k`-th derivative (`k = 1, 2, 3`) of `θ ↦ log P_{im}(θ)` is the Fréchet
derivative `iteratedFDeriv ℝ k`, a `k`-linear map on `ℝ^K`, measured in the operator norm,
with `z` and `θ` in the Euclidean norm. The three bounds are the single statement
`‖D^k log P_{im}(θ)‖ ≤ (2M)^k`. Only the boundedness part of Axiom 7 is assumed. -/
theorem logProb_deriv_bounds {K : ℕ} (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (hB : IsBounded D Jstar M) (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (m : ℕ) (i : Fin (D.J m))
    (θ : EuclideanSpace ℝ (Fin K)) :
    ‖iteratedFDeriv ℝ k (fun θ' => Real.log (prob D m i θ')) θ‖ ≤ (2 * M) ^ k := by sorry

end McFadden1974.Asymptotics
