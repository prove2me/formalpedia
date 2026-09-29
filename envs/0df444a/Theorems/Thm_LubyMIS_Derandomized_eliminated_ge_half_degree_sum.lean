-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_eliminated_ge_half_degree_sum
-- name    : LubyMIS.Derandomized.eliminated_ge_half_degree_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:56:39.425993+00:00
-- url     : https://prove2.me/theorems/162e6bee-be29-424e-8a6e-c89aaae66ac2
-- title:
--   Proof of Theorem 1, first display — E[Y_k − Y_{k+1}] ≥ ½ Σ d(i)·Pr[i ∈ I′ ∪ N(I′)] ≥ ½ Σ d(i)·Pr[i ∈ N(I′)]
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph and let $I'$ be a random subset of $V'$ on a probability space, such that each event $\{i \in I'\}$ is measurable. Then the expected number of edges with at least one endpoint in $I' \cup N(I')$ satisfies
--   $$E[Y_k - Y_{k+1}] \ \ge\ \tfrac12 \sum_{i \in V'} d(i)\,\Pr[i \in I' \cup N(I')] \ \ge\ \tfrac12 \sum_{i \in V'} d(i)\,\Pr[i \in N(I')].$$
--
--   Every eliminated edge has at least one and at most two endpoints in $I' \cup N(I')$, and each vertex is incident to $d(i)$ edges. This display reduces Theorems 1, 2 and 3 to lower bounds on the probabilities $\Pr[i \in N(I')]$.
--
--   **Formalization Note** The statement is proved in the paper for Algorithm B's selection; it is stated here for an arbitrary random selection $I' = S(\omega)$ with measurable membership events, which contains the page's instance. Since the number of eliminated edges takes finitely many values, it is integrable, so the Bochner integral is the expectation. The companion mission states the same display with finitely supported weights instead of a measure.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1041, §3.4, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

/-- First display of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), for an arbitrary random
selection `I′ = S ω` on a probability space `(Ω, μ)`:
`E[Y_k − Y_{k+1}] ≥ ½ ∑_i d(i) Pr[i ∈ I′ ∪ N(I′)] ≥ ½ ∑_i d(i) Pr[i ∈ N(I′)]`. -/
theorem eliminated_ge_half_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Ω → Finset V) (hS : ∀ i, MeasurableSet {ω | i ∈ S ω}) :
    (∫ ω, (eliminated H (S ω) : ℝ) ∂μ) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} ∧
      1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ nbhd H (S ω)} := by sorry

end LubyMIS.Derandomized
