-- Prove2me | Theorems.Thm_GittinsUCB_Patient_equation_2
-- name    : GittinsUCB.Patient.equation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:21.804266+00:00
-- url     : https://prove2.me/theorems/78836a89-8257-461c-b24c-1a0a75ea5163
-- title:
--   Equation (2) — posterior-mean reward identity
-- statement:
--   For each stopping time $\tau\ge1$ based on observed rewards, replacing the latent quality $\theta$ by its posterior mean $\mu_t$ does not change the expected discounted stopped reward:
--
--   $$\mathbb E\!\left[\sum_{t=0}^{\tau}\gamma^t(\theta-\lambda)\right]
--   =\mathbb E\!\left[\sum_{t=0}^{\tau}\gamma^t(\mu_t-\lambda)\right],\qquad 0<\gamma<1.$$
--
--   Taking suprema over the same retirement times gives the second equality of equation (2), and connects the posterior recursion to the stochastic model.
--
--   **Formalization Note** The prior and observation-noise variances are positive. The integral is taken under the canonical Gaussian model, and $\tau$ is a stopping time of the reward filtration.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 2, equation (2), second equality; pp. 9–10, Appendix A.3

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Equation (2), second equality, for each admissible stopping time. -/
theorem equation_2 (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ lam μ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (σ2 : ℝ≥0) (hσ : 0 < σ2) (τ : Ω → ℕ∞)
    (hτ : IsRetirementTime τ) :
    (∫ ω, stoppedReward γ lam (fun _ => θ) τ ω ∂(model μ σ2 σW2)) =
      ∫ ω, stoppedReward γ lam (postMean μ (σ2 : ℝ) (σW2 : ℝ)) τ ω
        ∂(model μ σ2 σW2) := by sorry

end GittinsUCB.Patient
