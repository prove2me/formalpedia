-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_small_mass_gaussian
-- name    : LinParamBandits.PEGE.small_mass_gaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:26.107976+00:00
-- url     : https://prove2.me/theorems/77a986fa-170b-4dd3-8156-61d6652a385a
-- title:
--   Lemma 3.2(b) — for Z ~ N(0, I_r/r), E[‖Z‖] ≤ 1 and E[1/‖Z‖] ≤ √π
-- statement:
--   Let $r \ge 2$ and let $Z$ have the multivariate normal distribution on $\mathbb R^r$ with mean $0$ and covariance matrix $I_r/r$. Then
--   $$\mathbb E\big[\|Z\|\big] \le 1 \qquad\text{and}\qquad \mathbb E\big[1/\|Z\|\big] \le \sqrt\pi.$$
--
--   So the prior of the lower bound of Theorem 2.1 satisfies the moment hypothesis of the risk bound of Theorem 3.1 with $M = \sqrt\pi$, uniformly in $r$.
--
--   **Formalization Note** $N(0, I_r/r)$ is the law of $Y/\sqrt r$ with $Y$ standard normal on $\mathbb R^r$. Both expectations are lower Lebesgue integrals.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 3.2(b), p. 16 (proof App. A.2, p. 28)

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Lemma 3.2(b) (Small Mass Near the Origin), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 16: if `Z` has the multivariate normal distribution with mean `0 ∈ ℝ^r` and
covariance matrix `I_r / r`, then `E[‖Z‖] ≤ 1` and `E[1/‖Z‖] ≤ √π`. -/
theorem small_mass_gaussian (r : ℕ) (hr : 2 ≤ r) :
    ∫⁻ z, ‖z‖ₑ ∂(gaussPrior r) ≤ 1 ∧
      ∫⁻ z, ‖z‖ₑ⁻¹ ∂(gaussPrior r) ≤ ENNReal.ofReal (Real.sqrt Real.pi) := by sorry
end LinParamBandits.PEGE
