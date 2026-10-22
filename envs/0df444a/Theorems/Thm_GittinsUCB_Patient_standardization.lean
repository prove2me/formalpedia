-- Prove2me | Theorems.Thm_GittinsUCB_Patient_standardization
-- name    : GittinsUCB.Patient.standardization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:26.37858+00:00
-- url     : https://prove2.me/theorems/a644b961-cea1-4223-83cd-494261289678
-- title:
--   §3.2 — location-scale identity for the index
-- statement:
--   For a Gaussian arm with prior mean $\mu$, positive prior variance $\sigma^2$, and positive noise variance $\sigma_W^2$, changing location and scale gives
--
--   $$\lambda_\gamma(\mu,\sigma^2;\sigma_W^2)
--   =\mu+\sigma\lambda_\gamma(0,1;\sigma_W^2/\sigma^2),\qquad 0<\gamma<1.$$
--
--   This reduces the main asymptotic result to a standard-normal prior while retaining an arbitrary noise-to-signal ratio.
--
--   **Formalization Note** The paper suppresses the noise variance in its usual index notation; here it is displayed explicitly. The corresponding GGW Theorem 7.13 on the platform concerns a different conjugate-sampling model, so this statement uses the present paper's fair-tax model.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 4, §3.2 (stated; proof cited to [8])

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Section 3.2: change of location and scale of the prior and observations. -/
theorem standardization (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ μ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (σ2 : ℝ≥0) (hσ : 0 < σ2) :
    gittinsIndex σW2 γ μ σ2 = μ + Real.sqrt (σ2 : ℝ) *
      gittinsIndex (σW2 / σ2) γ 0 1 := by sorry

end GittinsUCB.Patient
