-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_expected_score_eq_zero
-- name    : McFadden1974.Asymptotics.expected_score_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:36.299054+00:00
-- url     : https://prove2.me/theorems/5ee1a400-1e80-4c2c-a572-1b6d3c1cbdc0
-- title:
--   Equation (46) — the score of each observation has mean zero at the true parameter
-- statement:
--   Let the choice $Y_m$ at observation $m$ be drawn from the conditional logit probabilities at the true parameter $\theta^0$, and let $\lambda^m(\theta) = \log P_{Y_m m}(\theta)$ be the log-likelihood contribution (44) of that observation. Then the score $\lambda^m_\theta(\theta^0) = \nabla_\theta \lambda^m(\theta^0)$ is integrable and
--   $$E\,\lambda^m_\theta(\theta^0) = \Bigl[\sum_{i=1}^{J_m} \frac{\partial P_{im}}{\partial\theta}\Bigr]_{\theta^0} = 0 .$$
--
--   Mean-zero scores make $L^q_\theta(\theta^0)$ a sum of independent centred random vectors, to which the law of large numbers and the central limit theorem apply.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 136, Equation (46) (Lemma 6, proof); PDF p. 32

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Equation (46)** (Lemma 6, proof, p. 136, PDF p. 32): "Further, (46)
Eλ_θ^m(θ⁰) = [Σ_{i=1}^{J_{n_m}} ∂P_{in_m}/∂θ]_{θ⁰} = 0." Here `λ^m(θ) = log P_{Y_m m}(θ)` is the
log-likelihood contribution (44) of observation `m`, and `λ_θ^m` its gradient.

Formalization Note: the expectation is the Bochner integral of the `ℝ^K`-valued random vector
`ω ↦ ∇_θ log P_{Y_m(ω) m}(θ⁰)`; its integrability is part of the conclusion, so the identity is
not the junk value of a non-integrable integrand. The choices follow the sampling model
`IsLogitSample` at the true parameter `θ⁰`. -/
theorem expected_score_eq_zero {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (m : ℕ) :
    Integrable (fun ω => gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀) μ ∧
      ∫ ω, gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀ ∂μ = 0 := by sorry

end McFadden1974.Asymptotics
