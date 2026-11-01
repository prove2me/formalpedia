-- Prove2me | Theorems.Thm_IDEPoA_lemma_3_2_window
-- name    : IDEPoA.lemma_3_2_window
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:30.74781+00:00
-- url     : https://prove2.me/theorems/c5388240-3b5c-482c-929b-a3efa6aec26e
-- title:
--   Lemma 3.2, window form: $Z(\theta)\ge Z(\zeta)+\min\{F^\Delta(\zeta),\theta-\zeta-P\}$ while only descending edges receive flow
-- statement:
--   Let $f$ be a feasible flow. Let $h:V\to\mathbb N$ be a level function with $h(t)=0$, $h(v)\ge1$ for $v\ne t$, and $h\le P$ for a number $P\in\mathbb N$. Let $A$ be a set of edges with
--   $$h(w)+\tau_e\le h(v)\quad\text{for all }e=vw\in A,$$
--   and let $0\le\zeta\le\zeta'$ be such that
--
--   1. every edge $e=vw\notin A$ with $F_e^\Delta(\zeta)>0$ satisfies $h(w)+\tau_e\le P$;
--   2. $f_e^+(\theta)=0$ for all $\theta\in[\zeta,\zeta']$ and all $e\notin A$.
--
--   Then for all $\theta\in[\zeta,\zeta']$
--   $$Z(\theta)\ge Z(\zeta)+\min\{F^\Delta(\zeta),\ \theta-\zeta-P\}.$$
--
--   Thus the volume present at time $\zeta$ reaches the sink at rate at least $1$ after a delay of at most $P$, as long as the flow only uses edges that descend in the levels. This is the form of Lemma 3.2 that Corollary 3.7 and display (11) use. They apply the lemma to a flow in a cyclic graph from an intermediate time, when edges outside the shortest-path subgraph may still hold flow.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - generalization: Lemma 3.2 and Claim 1: an acyclic network, from level function d̃ and for all times → any graph, any level function h, a time window in which only descending edges receive flow, with a condition on the other edges holding flow at time ζ; reason: for A = E and h = d̃ it gives the printed inequality of Lemma 3.2; Corollary 3.7 and (11) need this form, since they apply Lemma 3.2 in a cyclic graph
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, proof of Lemma 3.2, Claim 1, display (8), pp.13–15

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The window form of Lemma 3.2 (Graf & Harks, arXiv:2007.07794v2, proof of Lemma 3.2, pp.13–15;
the claim it generalizes is Claim 1, display (8), p.13). Let `h : V → ℕ` be a level function with
`h t = 0`, `h v ≥ 1` otherwise, and bounded by `P`. Let `ζ ≤ ζ'` be a time window during which only
the edges in `A` receive flow, every edge `e ∈ A` descends, `h(head e) + τₑ ≤ h(tail e)`, and every
other edge that holds flow at time `ζ` satisfies `h(head e) + τₑ ≤ P`. Then on the window
`Z(θ) ≥ Z(ζ) + min {F^Δ(ζ), θ − ζ − P}`.

This form is what Corollary 3.7 and display (11) need: both apply Lemma 3.2 to a flow in a cyclic
graph from an intermediate time, where edges outside the shortest-path subgraph may still hold
flow. It contains Lemma 3.2 (`A = E`, `ζ'` arbitrary, `h` the pessimistic remaining distance
`d̃`). -/
theorem lemma_3_2_window (N : FlowNetwork V E) (hN : Standing N) (f : Flow E)
    (hf : IsFeasible N f) (h : V → ℕ) (ht : h N.t = 0) (hpos : ∀ v, v ≠ N.t → 1 ≤ h v)
    (A : Set E) (hA : ∀ e ∈ A, h (N.head e) + N.τ e ≤ h (N.tail e)) (P : ℕ)
    (hP : ∀ v, h v ≤ P) (ζ ζ' : ℝ) (hζ : 0 ≤ ζ) (hζζ' : ζ ≤ ζ')
    (hload : ∀ e, e ∉ A → 0 < load f e ζ → h (N.head e) + N.τ e ≤ P)
    (hwindow : ∀ θ ∈ Icc ζ ζ', ∀ e, e ∉ A → f.fplus e θ = 0) :
    ∀ θ ∈ Icc ζ ζ', Z N f θ ≥ Z N f ζ + min (totalLoad f ζ) (θ - ζ - P) := by sorry

end IDEPoA
