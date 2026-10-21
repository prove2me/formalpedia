-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_ode_consensus
-- name    : NaiveLearn.OverMatch.ode_consensus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:17.306314+00:00
-- url     : https://prove2.me/theorems/1669ebdd-3491-4873-915a-a4a51a56affe
-- title:
--   Proof of Lemma 3, p. 21 — the solution of ż = (W − I)z converges to the consensus 1⟨µ^W, x⟩
-- statement:
--   Let $W$ be the weight matrix of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$) with centrality measure $\mu^W$, and let $z$ solve the linear equation (7),
--   $$
--   \dot z(t)=(W-I)\,z(t),\qquad z(0)=\mathbf x .
--   $$
--   Then
--   $$
--   \lim_{t\to\infty}z(t)=\mathbf 1\,\langle\mu^W,\mathbf x\rangle ,
--   $$
--   the consensus vector all of whose coordinates equal $\langle\mu^W,\mathbf x\rangle=\sum_i\mu^W_ix_i$.
--
--   This is the deterministic consensus of the mean-field dynamics of probability matching; Lemma 4 compares the extremization dynamics with it.
--
--   **Formalization Note** The statement is posed for every initial vector $\mathbf x\in\mathbb R^m$ (the paper uses $\mathbf x\in[0,1]^m$); the equation is linear, so this is the same fact. Convergence is in the sup norm.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 21, proof of Lemma 3, (7)

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Proof of Lemma 3, p. 21: the solution of `ż = (W − I) z`, `z(0) = x` (equation (7)), converges
to the consensus vector `1⟨µ^W, x⟩`. -/
theorem ode_consensus {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) (x : Fin m → ℝ)
    (z : ℝ → (Fin m → ℝ)) (hz : IsODESolution (fun v => W.mulVec v - v) z) (hz0 : z 0 = x) :
    Tendsto z atTop (𝓝 (fun _ => ∑ i, μ i * x i)) := by sorry

end NaiveLearn.OverMatch
