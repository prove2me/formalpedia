-- Prove2me | Theorems.Thm_McFadden1974_QPTest_axiom6_iff_qp_min_zero
-- name    : McFadden1974.QPTest.axiom6_iff_qp_min_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:47:26.707893+00:00
-- url     : https://prove2.me/theorems/0681a71a-f306-420d-8526-0cd26a07fb7e
-- title:
--   Lemma 4 — Axiom 6 iff the quadratic-program minimum is zero
-- statement:
--   Consider a finite conditional-logit experiment satisfying Axiom 5. Let $Q$ be the set of vectors $y=\sum_{n,i,j}\alpha_{ijn}S_{in}(z_{jn}-z_{in})$ with every $\alpha_{ijn}\geq1$. Then Axiom 6 holds exactly when the quadratic program attains zero:
--   $$
--   \left[\nexists\gamma\ne0:\ S_{in}(z_{jn}-z_{in})\cdot\gamma\leq0\ \text{for every }n,i,j\right]
--   \quad\Longleftrightarrow\quad
--   \min_{y\in Q}\|y\|^2=0.
--   $$
--   This converts the existence condition for the conditional-logit maximum likelihood estimate into a finite quadratic-programming test.
--
--   **Formalization Note** The minimum is required to be attained, as in the paper; a mere infimum of zero would state less. The data convention includes at least one observed choice in each trial.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 117, Lemma 4 and Equation (22) (PDF p. 13)

import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false

namespace McFadden1974.QPTest

/-- McFadden (1974), p. 117 (PDF 13), Lemma 4 and equation (22).
Under Axiom 5, Axiom 6 holds exactly when the quadratic program attains a
minimum of zero. `IsLeast` retains attainment, unlike an infimum equation.
The finite data model includes at least two alternatives and at least one
observed choice per trial; Axiom 5 uses the equivalent difference span form. -/
theorem axiom6_iff_qp_min_zero {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) :
    d.Axiom6 ↔
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by sorry

end McFadden1974.QPTest
