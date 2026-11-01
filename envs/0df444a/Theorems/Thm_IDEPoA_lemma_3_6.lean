-- Prove2me | Theorems.Thm_IDEPoA_lemma_3_6
-- name    : IDEPoA.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:24.966146+00:00
-- url     : https://prove2.me/theorems/fa2460ce-bff0-4f09-8024-877bd9a7d710
-- title:
--   Lemma 3.6: in a sink-like subgraph only physically shortest paths can be active
-- statement:
--   Let $f$ be a feasible flow and let $T$ be sink-like on $[\theta_1,\theta_2]$. Then at every time $\hat\theta\in[\theta_1,\theta_2]$, for every node $v\in T$, all active $v$-$t$ paths are physically shortest, and moreover
--   $$\sum_{e\in E(T)}F_e^\Delta(\hat\theta)<\frac12.$$
--
--   Within a sink-like subgraph the flow thus follows the static shortest-path structure, as in an acyclic network.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - reading: flow f left implicit → f any feasible flow; reason: the proof uses feasibility only
--   - generalization: the conclusion on active paths → also ∑ over E(T) of the loads at θ̂ is below 1/2; reason: this is the bound in the page's proof, which Claim 3 uses as well
--   - encoding: an induced subgraph T ⊆ G on an interval [θ1, θ2] → a node set T with t ∈ T and 0 ≤ θ1 ≤ θ2; reason: the conclusion is vacuous for empty T; a nonempty T with the first property contains t
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Lemma 3.6, p.17

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Lemma 3.6 (Graf & Harks, arXiv:2007.07794v2, p.17): if `T` is sink-like on `[θ₁, θ₂]`, then
during this interval only physically shortest paths towards `t` can be active. The second conjunct
is the bound `∑_{e ∈ E(T)} Fₑ^Δ(θ̂) < 1/2` of the page's proof, which Claim 3 uses as well. -/
theorem lemma_3_6 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f)
    (T : Finset V) (θ₁ θ₂ : ℝ) (hT : IsSinkLike N f T θ₁ θ₂) (θhat : ℝ)
    (hθhat : θhat ∈ Icc θ₁ θ₂) :
    (∀ v ∈ T, ∀ Q, IsActiveWalk N f θhat v Q → physLength N Q = physDist N v) ∧
      ∑ e ∈ edgesIn N T, load f e θhat < 1 / 2 := by sorry

end IDEPoA
