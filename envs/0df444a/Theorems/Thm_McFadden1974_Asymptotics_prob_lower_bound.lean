-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_prob_lower_bound
-- name    : McFadden1974.Asymptotics.prob_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:47:51.60888+00:00
-- url     : https://prove2.me/theorems/9cdd7d9f-58ee-4cfb-a418-4cf74a0a1419
-- title:
--   Equation (42) — logit selection probabilities are bounded below by $1/(J_* e^{2M|\theta|})$
-- statement:
--   Suppose every observation $m$ has at most $J_*$ alternatives and every vector of independent variables satisfies $|z_{im}| \le M$ (the boundedness part of Axiom 7). Then for every observation $m$, alternative $i$ and parameter $\theta \in \mathbb R^K$ the conditional logit selection probability satisfies
--   $$P_{im}(\theta) \ \ge\ \frac{1}{J_*\, e^{2M|\theta|}} \;=\; P_* > 0 .$$
--
--   The bound is uniform in the observation, so on bounded sets of parameters every alternative has probability bounded away from zero. It drives the probability estimate in the proof of Lemma 5.
--
--   **Formalization Note** The printed $1/J_*e^{2M|\theta|}$ is read as $1/(J_* e^{2M|\theta|})$. Norms are Euclidean.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 135, Equation (42) (Lemma 5, proof); PDF p. 31

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Equation (42)** (Lemma 5, proof, p. 135, PDF p. 31): "The selection probabilities are
bounded below by (42) P_in ≥ 1/J_* e^{2M|θ|} ≡ P_* > 0, where J_* and M are the bounds given by
Axiom 7."

Formalization Note: the printed `1/J_* e^{2M|θ|}` is read as `1/(J_* e^{2M|θ|})`. Only the
boundedness part of Axiom 7 is assumed (`IsBounded`), with Euclidean norms on `z` and `θ`.
`J_* ≥ J_m ≥ 1`, so the bound is a positive real number; the bound holds for every observation,
alternative and parameter. -/
theorem prob_lower_bound {K : ℕ} (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (hB : IsBounded D Jstar M) (m : ℕ) (i : Fin (D.J m)) (θ : EuclideanSpace ℝ (Fin K)) :
    1 / ((Jstar : ℝ) * Real.exp (2 * M * ‖θ‖)) ≤ prob D m i θ := by sorry

end McFadden1974.Asymptotics
