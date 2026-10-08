-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_expected_hessian_eq
-- name    : McFadden1974.Asymptotics.expected_hessian_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:13.058989+00:00
-- url     : https://prove2.me/theorems/e1ed2617-a4ec-45c9-8519-3bfb7e0a16e6
-- title:
--   Equation (47) — the expected Hessian of each observation's log-likelihood is $-\Omega_m$
-- statement:
--   Let $Y_m$ be drawn from the conditional logit probabilities at $\theta^0$ and $\lambda^m(\theta) = \log P_{Y_m m}(\theta)$. Then the Hessian of $\lambda^m$ at $\theta^0$ has expectation
--   $$E\,\lambda^m_{\theta\theta'}(\theta^0) = -\Omega_m, \qquad \Omega_m = \sum_{i=1}^{J_m} (z_{im}-\bar z_m)'\,P_{im}\,(z_{im}-\bar z_m),$$
--   with $P_{im}$ and $\bar z_m$ evaluated at $\theta^0$.
--
--   Together with Axiom 7, this identifies the limit $\Omega$ of $\frac1q\sum_{m<q}\Omega_m$ as the asymptotic information matrix per observation.
--
--   **Formalization Note** The Hessian is the second Fréchet derivative, and the identity is stated as the equality of bilinear forms: for all directions $u, v$, $E\,D^2\lambda^m(\theta^0)[u,v] = -u'\Omega_m v$, with integrability of the integrand included.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 136, Equation (47) (Lemma 6, proof); PDF p. 32

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix

/-- **Equation (47)** (Lemma 6, proof, p. 136, PDF p. 32): "Define
Ω_m = −Eλ_θθ'^m(θ⁰) = Σ_{i=1}^{J_{n_m}} (z_{in_m} − z̄_{n_m})' P_{in_m} (z_{in_m} − z̄_{n_m})."
The content is the equality: the expected Hessian of `λ^m(θ) = log P_{Y_m m}(θ)` at `θ⁰` is
minus the moment matrix (47).

Formalization Note: the Hessian is the second Fréchet derivative `iteratedFDeriv ℝ 2`, a
bilinear form on `ℝ^K`; the identity is stated for every pair of directions `u, v`, against
the bilinear form `uᵀ Ω_m v` of `momentMatrix D θ⁰ m`. Integrability of each entry is part of the
conclusion. The choices follow `IsLogitSample` at `θ⁰`. -/
theorem expected_hessian_eq {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (m : ℕ) (u v : EuclideanSpace ℝ (Fin K)) :
    Integrable (fun ω =>
        iteratedFDeriv ℝ 2 (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀ ![u, v]) μ ∧
      ∫ ω, iteratedFDeriv ℝ 2 (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀ ![u, v] ∂μ =
        -(WithLp.ofLp u ⬝ᵥ (momentMatrix D θ₀ m *ᵥ WithLp.ofLp v)) := by sorry

end McFadden1974.Asymptotics
