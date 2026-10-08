-- Prove2me | Theorems.Thm_McFadden1974_QPTest_zero_min_implies_axiom6
-- name    : McFadden1974.QPTest.zero_min_implies_axiom6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:46:35.5113+00:00
-- url     : https://prove2.me/theorems/02594cf3-3bd0-4432-8054-3831932fc707
-- title:
--   Lemma 4, proof — zero quadratic-program minimum implies Axiom 6
-- statement:
--   Let the choice data satisfy Axiom 5, and suppose that the zero vector is feasible for the quadratic program (22). Then Axiom 6 holds:
--   $$
--   \left[0\in Q\right]\Longrightarrow\left[\forall\gamma\in\mathbb R^K,\ (\forall n,i,j,\ w_{nij}\cdot\gamma\leq0)\Longrightarrow\gamma=0\right].
--   $$
--   Since the objective is $\|y\|^2$, feasibility of zero means that the program attains a zero minimum. This is the necessity direction of Lemma 4.
--
--   **Formalization Note** Each trial has at least one observed choice; this makes the paper's strict-inequality step follow from Axiom 5.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 117, Lemma 4, proof, first paragraph (PDF p. 13)

import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false

namespace McFadden1974.QPTest

/-- McFadden (1974), p. 117 (PDF 13), Lemma 4, proof, first paragraph.
With Axiom 5, an attained zero value in (22) implies Axiom 6. Positivity of
each trial's repetition count is part of `ChoiceData`, as on p. 114. -/
theorem zero_min_implies_axiom6 {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) (h0 : (0 : EuclideanSpace ℝ (Fin K)) ∈ d.qpFeasible) :
    d.Axiom6 := by sorry

end McFadden1974.QPTest
