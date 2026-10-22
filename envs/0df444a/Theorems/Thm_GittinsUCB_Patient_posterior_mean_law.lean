-- Prove2me | Theorems.Thm_GittinsUCB_Patient_posterior_mean_law
-- name    : GittinsUCB.Patient.posterior_mean_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:21.396179+00:00
-- url     : https://prove2.me/theorems/31764c3e-b0af-4ff9-8080-d8d8150184fe
-- title:
--   §3.4 — law of the posterior mean
-- statement:
--   For a unit-variance prior $N(\mu_0,1)$, the posterior mean after $L$ rewards is Gaussian with mean $\mu_0$ and variance $1-\sigma_L^2$:
--
--   $$\mu_L\sim N(\mu_0,1-\sigma_L^2).$$
--
--   This law identifies the distribution of the posterior-mean positive part in the lower index bound.
--
--   **Formalization Note** The claim includes $L=0$, when both sides are the point mass at $\mu_0$. The function mapped under the model is the explicitly defined posterior recursion.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 6, §3.4, paragraph following the explore-then-commit bound

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Section 3.4: the distribution of the posterior mean at time `L`. -/
theorem posterior_mean_law (σW2 : ℝ≥0) (hW : 0 < σW2)
    (L : ℕ) (μ0 : ℝ) :
    (model μ0 1 σW2).map (postMean μ0 1 (σW2 : ℝ) L) =
      gaussianReal μ0 (1 - postVar 1 (σW2 : ℝ) L).toNNReal := by sorry

end GittinsUCB.Patient
