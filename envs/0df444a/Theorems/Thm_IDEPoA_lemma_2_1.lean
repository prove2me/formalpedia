-- Prove2me | Theorems.Thm_IDEPoA_lemma_2_1
-- name    : IDEPoA.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:18.135133+00:00
-- url     : https://prove2.me/theorems/51e97593-8fb5-499b-a394-68c8088473e8
-- title:
--   Lemma 2.1: flow volume balance on a node set
-- statement:
--   Let $f$ be a feasible flow and $\theta\ge0$. For every set $W\subseteq V$ of nodes,
--   $$\sum_{e\in E(W)}F_e^\Delta(\theta)=\sum_{e\in\delta_W^-}F_e^-(\theta)+\sum_{v\in W\setminus\{t\}}U_v(\theta)-\sum_{e\in\delta_W^+}F_e^+(\theta)-\begin{cases}Z(\theta),&t\in W,\\0,&\text{else,}\end{cases}$$
--   where $E(W)$ is the set of edges with both ends in $W$, and $\delta_W^+$, $\delta_W^-$ are the sets of edges leaving and entering $W$. In particular
--   $$F^\Delta(\theta)=\sum_{v\ne t}U_v(\theta)-Z(\theta).$$
--
--   This is the bookkeeping identity behind the monotonicity of the total flow volume and behind all volume estimates for sink-like subgraphs.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: sum over v ∈ W of Uv → sum over v ∈ W ∖ {t}; reason: Ut is not defined; the proof on p.9 sums over U ∖ {t}
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Lemma 2.1, p.9

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Lemma 2.1 (Graf & Harks, arXiv:2007.07794v2, p.9): the flow volume balance on `E(W)` for every
`W ⊆ V`, and `F^Δ(θ) = ∑_{v ≠ t} Uᵥ(θ) − Z(θ)`.

**Formalization Note.** The sum over `v ∈ W` of the page runs over `W ∖ {t}`, as `U_t` is not
defined; the page's proof does the same. -/
theorem lemma_2_1 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∀ W : Finset V,
      ∑ e ∈ edgesIn N W, load f e θ =
        ∑ e ∈ into N W, Fminus f e θ + ∑ v ∈ W.erase N.t, cumU N v θ
          - ∑ e ∈ outOf N W, Fplus f e θ - (if N.t ∈ W then Z N f θ else 0)) ∧
    totalLoad f θ = ∑ v ∈ Finset.univ.erase N.t, cumU N v θ - Z N f θ := by sorry

end IDEPoA
