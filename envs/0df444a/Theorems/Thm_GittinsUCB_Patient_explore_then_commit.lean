-- Prove2me | Theorems.Thm_GittinsUCB_Patient_explore_then_commit
-- name    : GittinsUCB.Patient.explore_then_commit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:22.94545+00:00
-- url     : https://prove2.me/theorems/00513582-d490-493d-906f-f1a18c2491d8
-- title:
--   §3.4 — explore-then-commit lower value bound
-- statement:
--   With unit-variance prior, explore for $L$ periods, then retire if $\mu_L<\lambda$ and otherwise continue playing. For $L\ge2$ and $0<\gamma<1$, the resulting value bound is
--
--   $$V^\lambda_\gamma(0,1;\sigma_W^2)
--   \ge-\sum_{t=0}^{L-1}\gamma^t\lambda
--   +\frac{\gamma^L}{1-\gamma}\mathbb E[(\mu_L-\lambda)^+].$$
--
--   For $\lambda\ge0$, this also yields
--
--   $$V^\lambda_\gamma(0,1;\sigma_W^2)
--   \ge-L\lambda+\frac{\gamma^L}{1-\gamma}\mathbb E[(\mu_L-\lambda)^+].$$
--
--   These are the paper's two consecutive lower bounds on the stopping value.
--
--   **Formalization Note** $L\ge2$ makes the policy compatible with the printed $\tau\ge1$ convention, and $\lambda\ge0$ is needed only for the second bound.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 6, §3.4, displayed bound before the posterior-mean law

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Section 3.4: the two explore-then-commit value bounds. -/
theorem explore_then_commit (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ lam : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (L : ℕ) (hL : 2 ≤ L) :
    (-(∑ t ∈ Finset.range L, γ ^ t * lam) +
      γ ^ L / (1 - γ) *
        ∫ ω, max (postMean 0 1 (σW2 : ℝ) L ω - lam) 0
          ∂(model 0 1 σW2) ≤ value σW2 γ lam 0 1) ∧
    (0 ≤ lam →
      -(L : ℝ) * lam + γ ^ L / (1 - γ) *
        ∫ ω, max (postMean 0 1 (σW2 : ℝ) L ω - lam) 0
          ∂(model 0 1 σW2) ≤ value σW2 γ lam 0 1) := by sorry

end GittinsUCB.Patient
