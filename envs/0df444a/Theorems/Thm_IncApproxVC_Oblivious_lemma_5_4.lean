-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_5_4
-- name    : IncApproxVC.Oblivious.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:13.569669+00:00
-- url     : https://prove2.me/theorems/1f3506de-0112-44c7-b333-9ac298ab8385
-- title:
--   Lemma 5.4 — lower-bounding flow on a sink edge: some flow of value $\ge F$ keeps at least $f(e)$ on $e$
-- statement:
--   Let $G=(V,E,u)$ be a flow network with positive capacities and no lower bounds, with source $s$ and sink $t$, whose maximum $s$–$t$ flow has value at least $F$. Fix a sink edge $e\in\partial^-_G(t)$ (an edge into $t$ from another vertex). If $f$ is a feasible $s$–$t$ flow, then there is an $s$–$t$ flow $f'$ with
--   $$|f'|\ \ge\ F\qquad\text{and}\qquad f'(e)\ \ge\ f(e).$$
--   In Algorithm 2 this justifies raising the lower bound of a saturated sink edge: it never destroys a flow of value $F$.
--
--   **Formalization Note.** The network may have parallel edges (`FlowNet`, with lower bounds $0$). A feasible flow is an $s$–$t$ flow of some value $|f|$.
--
--   Differences from the source:
--   - reading: there exists a flow f′ of value |f| ≥ F → an s–t flow f′ with |f′| ≥ F and f′(e) ≥ f(e); reason: obvious typo: the proof concludes |f′| ≥ F, and |f| ≥ F is false in general (f = 0, F > 0); INSIGHTS I5
--   - reading: f is some feasible flow → f is a feasible s–t flow (0 ≤ f ≤ u, conservation outside s, t) of some value; reason: the proof runs Ford–Fulkerson starting from f, which needs an s–t flow
--   - encoding: any graph G = (V, E, u) → a FlowNet with a finite edge type (parallel edges allowed) and lower bounds 0; reason: flow graphs are capacitated (multi-)graphs, p. 13; a simple graph is a special case
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 17, Lemma 5.4

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Flow

namespace IncApproxVC.Oblivious

/-- **Lemma 5.4** (lower-bounding flow on sink edges), p. 17. Let `G = (V, E, u)` be a network with
positive capacities and no lower bounds, with source `s` and sink `t`, whose maximum `s–t` flow has
value at least `F`, and let `e ∈ ∂⁻_G(t)` be a sink edge. For every feasible `s–t` flow `f` there
is an `s–t` flow `f′` of value `|f′| ≥ F` with `f′(e) ≥ f(e)`. (The page prints `|f| ≥ F`; the
proof concludes `|f′| ≥ F`.) -/
theorem lemma_5_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (N : FlowNet V E)
    (hlow : ∀ e, N.low e = 0) (hup : ∀ e, 0 < N.up e) (s t : V) (F : ℝ)
    (hmax : N.MaxFlowAtLeast s t F) (e : E) (he : N.head e = t ∧ N.tail e ≠ t)
    (f : E → ℝ) (Ff : ℝ) (hf : N.IsSTFlow s t f Ff) :
    ∃ f' : E → ℝ, ∃ Ff' : ℝ, N.IsSTFlow s t f' Ff' ∧ F ≤ Ff' ∧ f e ≤ f' e := by sorry

end IncApproxVC.Oblivious
