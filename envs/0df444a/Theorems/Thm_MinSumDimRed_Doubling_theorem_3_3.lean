-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_theorem_3_3
-- name    : MinSumDimRed.Doubling.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:35:38.836091+00:00
-- url     : https://prove2.me/theorems/a67385a2-45c0-459d-a568-2afe3dfab087
-- title:
--   Theorem 3.3 — sparse subgraph theorem: edge probabilities $\le \delta \le \theta^7/600$ give a random $\theta$-everywhere-sparse induced subgraph losing each vertex with probability $\le \theta$
-- statement:
--   **Theorem 3.3** (Sparse Subgraph Theorem [MMR19, Theorem 3.2], p. 11). Let $X$ be a finite set and $H = (V, E)$ a random graph on a probability space $(\Omega, \mu)$: $V$ is a random subset of $X$ and $E$ a random set of edges between vertices of $V$; no independence assumptions are made. Let $\theta \in (0, 1/2)$ and $\delta \le \theta^7/600$, and assume $\Pr[(x, y) \in E] \le \delta$ for all $x, y \in X$. Then there is a random subset $V' \subseteq V$ on the same probability space such that
--
--   - $H[V']$ is $\theta$-everywhere sparse (every $u \in V'$ has at most $\theta |V'|$ neighbours in $V'$), for every outcome, and
--   - $\Pr[u \in V \setminus V'] \le \theta$ for every $u \in X$.
--
--   Differences from the source:
--   - reading: a random set E of edges between vertices in V; (x, y) ∈ E → E : Ω → SimpleGraph X (undirected, loopless) with every edge inside V ω and every event {ω | (E ω).Adj x y} measurable; (x, y) ∈ E is (E ω).Adj x y; reason: the graphs of the paper are undirected (the distortion graph is symmetric and has no loops); 'random' means a random variable
--   - encoding: finite set X; random subsets V, V' ⊆ X → a type X with [Fintype X]; V, V' : Ω → Finset X with measurable membership events (IsRandomSubset) and V' ω ⊆ V ω for every ω; reason: a random subset is a random variable on the same probability space
--   - encoding: H[V'] is θ-everywhere sparse → IsEverywhereSparseOn (E ω) (V' ω) θ for every ω; reason: Definition 3.2 for the induced subgraph, required pointwise as printed
--   - encoding: with probability at least p / Pr[event] ≤ q → p ≤ μ.real {ω | …} / μ.real {ω | …} ≤ q on a probability measure μ; reason: μ.real is the (outer) measure as a real number; no measurability of the event is presupposed, and for measurable events it is the probability
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 11 (PDF 11), Theorem 3.3

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Costs
import Definitions.Def_MinSumDimRed_Doubling_Random

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-- Theorem 3.3 (Sparse Subgraph Theorem [MMR19, Theorem 3.2]), p. 11: let `X` be a finite set
and `H = (V, E)` a random graph on one probability space, `V` a random subset of `X` and `E` a
random set of (undirected) edges between vertices of `V`, with no independence assumptions. Let
`θ ∈ (0, 1/2)` and assume `Pr[(x, y) ∈ E] ≤ δ` for all `x, y ∈ X`, where `δ ≤ θ^7/600`. Then
there is a random subset `V' ⊆ V` on the same probability space such that `H[V']` is
`θ`-everywhere sparse (for every outcome) and `Pr[u ∈ V \ V'] ≤ θ` for every `u ∈ X`. -/
theorem theorem_3_3
    {X : Type*} [Fintype X] [DecidableEq X]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Finset X) (hV : IsRandomSubset V)
    (E : Ω → SimpleGraph X)
    (hE_meas : ∀ x y : X, MeasurableSet {ω | (E ω).Adj x y})
    (hE_sub : ∀ ω x y, (E ω).Adj x y → x ∈ V ω ∧ y ∈ V ω)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hδ : δ ≤ θ ^ 7 / 600)
    (hprob : ∀ x y : X, μ.real {ω | (E ω).Adj x y} ≤ δ) :
    ∃ V' : Ω → Finset X, IsRandomSubset V' ∧ (∀ ω, V' ω ⊆ V ω) ∧
      (∀ ω, IsEverywhereSparseOn (E ω) (V' ω) θ) ∧
      ∀ u : X, μ.real {ω | u ∈ V ω ∧ u ∉ V' ω} ≤ θ := by sorry

end MinSumDimRed.Doubling
