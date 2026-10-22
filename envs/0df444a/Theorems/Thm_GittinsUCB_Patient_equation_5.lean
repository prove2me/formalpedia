-- Prove2me | Theorems.Thm_GittinsUCB_Patient_equation_5
-- name    : GittinsUCB.Patient.equation_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:23.548061+00:00
-- url     : https://prove2.me/theorems/0bb29e6a-8c73-4ed3-8dba-eac6b23d8413
-- title:
--   Equation (5) — noiseless-information upper bound
-- statement:
--   For a unit-variance standard-normal prior and any tax $\lambda$, a player allowed to observe the quality without noise has value
--
--   $$-\lambda+\frac\gamma{1-\gamma}\mathbb E[(\theta-\lambda)^+].$$
--
--   Therefore the original reward-adapted stopping value obeys
--
--   $$V^\lambda_\gamma(0,1;\sigma_W^2)
--   \le-\lambda+\frac\gamma{1-\gamma}\mathbb E[(\theta-\lambda)^+],\qquad 0<\gamma<1.$$
--
--   This is the information-relaxation input for the upper index bound.
--
--   **Formalization Note** The middle infinite sums printed in (5) omit discount factors; the formal statement records its outer value inequality and its correctly discounted noiseless expression.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 4, equation (5)

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Equation (5): the noiseless-information relaxation. -/
theorem equation_5 (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    value σW2 γ lam 0 1 ≤
      -lam + γ / (1 - γ) *
        ∫ ω, max (θ ω - lam) 0 ∂(model 0 1 σW2) := by sorry

end GittinsUCB.Patient
