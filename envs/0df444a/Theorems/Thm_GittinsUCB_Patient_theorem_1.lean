-- Prove2me | Theorems.Thm_GittinsUCB_Patient_theorem_1
-- name    : GittinsUCB.Patient.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:25.512714+00:00
-- url     : https://prove2.me/theorems/bcf32a1c-1543-48c8-b4e9-8aa2d6abee71
-- title:
--   Theorem 1 — Gittins index equals the prior upper quantile up to o(1)
-- statement:
--   Fix a prior mean $\mu\in\mathbb R$, positive prior variance $\sigma^2$, and positive observation-noise variance $\sigma_W^2$. Let $\sigma=\sqrt{\sigma^2}$, and let $\Phi^{-1}$ be the standard-normal quantile. Then
--
--   $$\lambda_\gamma(\mu,\sigma^2;\sigma_W^2)
--   =\mu+\sigma\Phi^{-1}(\gamma)+o(1)\qquad(\gamma\uparrow1).$$
--
--   The theorem identifies the patient-agent fair-tax index with the prior upper quantile to additive vanishing error. It is the goal of this mission.
--
--   **Formalization Note** The paper suppresses $\sigma_W^2$ in its index notation; Lean quantifies over it explicitly. Strict positivity of the prior variance supports the paper's standardization argument. The limit is one-sided because the discount factor is below one.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 3, Theorem 1, equation (4)

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Theorem 1: the Gaussian Gittins index matches the prior upper quantile. -/
theorem theorem_1 (σW2 : ℝ≥0) (hW : 0 < σW2)
    (μ : ℝ) (σ2 : ℝ≥0) (hσ : 0 < σ2) :
    Tendsto (fun γ : ℝ => gittinsIndex σW2 γ μ σ2 -
      (μ + stdQuantile γ * Real.sqrt (σ2 : ℝ)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by sorry

end GittinsUCB.Patient
