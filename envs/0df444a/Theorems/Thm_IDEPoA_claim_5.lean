-- Prove2me | Theorems.Thm_IDEPoA_claim_5
-- name    : IDEPoA.claim_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:10.532987+00:00
-- url     : https://prove2.me/theorems/80451910-d516-47a0-ad8a-9a8d9913252f
-- title:
--   Claim 5: little inflow into the sink makes the whole graph sink-like
-- statement:
--   Let $f$ be an IDE flow, $a\ge0$, $S=\sum_{e\in E}(\tau_e+\frac1{2\nu_e})$ and $b\ge a+S$. If the sink has a total cumulative inflow of less than $\frac12$ during $[a,b]$,
--   $$\sum_{e\in\delta_t^-}\int_a^bf_e^-(\theta)\,d\theta<\frac12,$$
--   then the whole graph is sink-like on $[a,b-S]$.
--
--   **Formalization Note** The inflow is the gross inflow through the edges into $t$. On an IDE it agrees with the increase of $Z$, since no edge leaving $t$ is ever active.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - reading: the sink node t has a total cumulative inflow of less than 1/2 → the gross inflow ∑ over δt− of the integrals of fe−; reason: no edge out of t is active, so it equals the increase of Z on an IDE
--   - reading: flow f left implicit → f an IDE flow; reason: the claim appears in the proof of Theorem 3.9, about IDE flows
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Claim 5, p.21

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Claim 5 (Graf & Harks, arXiv:2007.07794v2, p.21): for an IDE flow, if on an interval `[a, b]` of
length at least `∑ₑ (τₑ + 1/(2νₑ))` the sink has a total cumulative inflow of less than `1/2`, then
the whole graph is sink-like on `[a, b − ∑ₑ (τₑ + 1/(2νₑ))]`.

**Formalization Note.** The inflow into the sink is the gross `∑_{e ∈ δₜ⁻} ∫ₐᵇ fₑ⁻`. It agrees with
the increase of `Z` on an IDE, where no edge leaving `t` is ever active. -/
theorem claim_5 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsIDE N f) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a + weightSum N ≤ b)
    (hinflow : ∑ e ∈ inEdges N N.t, ∫ θ in a..b, f.fminus e θ < 1 / 2) :
    IsSinkLike N f Finset.univ a (b - weightSum N) := by sorry

end IDEPoA
