-- Prove2me | Theorems.Thm_LinParamBandits_LowerBound_norm_prob_bound
-- name    : LinParamBandits.LowerBound.norm_prob_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:00.704616+00:00
-- url     : https://prove2.me/theorems/d8366d30-952f-4812-8828-812db2389f93
-- title:
--   Lemma 2.4 — for Z ~ N(0, I_r/r), Pr{θ ≤ ‖Z‖ ≤ β} ≥ 1 − 4θ² − 1/β²
-- statement:
--   Let $r \ge 2$ and let $Z$ be a multivariate normal vector in $\mathbb R^r$ with mean $0$ and covariance matrix $I_r/r$, the prior of Section 2.
--
--   **Lemma 2.4.** For any $\theta \le 1/2$ and $\beta > 0$,
--   $$\Pr\{\theta \le \|Z\| \le \beta\} \;\ge\; 1 - 4\theta^2 - \frac{1}{\beta^2}.$$
--
--   The lemma keeps $\|Z\|$ away from $0$ and from $\infty$ with high probability; it is what turns the conditional bounds in the proof of Lemma 2.5 into an unconditional one.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm on `EuclideanSpace ℝ (Fin r)`, and the prior is the law of $Y/\sqrt r$ with $Y$ standard normal. As printed, $\theta$ may be zero or negative; the statement keeps that range. The hypothesis $r \ge 2$ is the paper's standing assumption (p. 3) and is needed: for $r = 1$ and small $\theta > 0$ the probability that $|Z| < \theta$ is about $0.8\,\theta$, which exceeds $4\theta^2$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 2.4, p. 11; proof in App. A.1, p. 27

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.LowerBound

/-- Lemma 2.4, Rusmevichientong, Tsitsiklis, arXiv:0812.3465v2, p. 11 (proof App. A.1, p. 27):
for `Z ~ N(0, I_r/r)` with `r ≥ 2`, any `θ ≤ 1/2` and `β > 0`,
`Pr{θ ≤ ‖Z‖ ≤ β} ≥ 1 − 4θ² − 1/β²`. -/
theorem norm_prob_bound (r : ℕ) (hr : 2 ≤ r) (θ β : ℝ) (hθ : θ ≤ 1 / 2) (hβ : 0 < β) :
    1 - 4 * θ ^ 2 - 1 / β ^ 2 ≤ (prior r).real {z | θ ≤ ‖z‖ ∧ ‖z‖ ≤ β} := by sorry

end LinParamBandits.LowerBound
