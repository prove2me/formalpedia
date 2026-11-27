-- Prove2me | Theorems.Thm_MalleableSched_Supplement_lemma_28
-- name    : MalleableSched.Supplement.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:41:06.904206+00:00
-- url     : https://prove2.me/theorems/94fccb6f-a455-4b4a-ae7a-bb4213345da0
-- title:
--   Lemma 28 (Hakimi, 1965) — every finite multigraph has an orientation with in-degree at least $\lfloor d(v)/2\rfloor$
-- statement:
--   Let $G=(V,E)$ be an undirected multigraph with finitely many edges; loops and parallel edges are allowed. For $v\in V$ let $d(v)$ be the degree of $v$, where a loop at $v$ counts twice. Then there is an orientation of $G$ (a choice of head among the two ends of every edge) such that every node $v\in V$ is the head of at least
--
--   $$
--   \left\lfloor \frac{d(v)}{2}\right\rfloor
--   $$
--
--   edges.
--
--   In the paper this lemma gives the orientation $D$ used in Step 3b of the algorithm for scaled matroid-rank speeds, on a graph that has parallel edges and loops.
--
--   **Formalization Note** The multigraph is the published `ContPatrol.Multigraph`: an edge $e$ has ends $\mathrm{src}(e)$ and $\mathrm{tgt}(e)$, and its degree counts a loop twice. An orientation is a Boolean per edge selecting the dart $(e,\mathrm{true})$ with head $\mathrm{tgt}(e)$ or $(e,\mathrm{false})$ with head $\mathrm{src}(e)$. The vertex type may be infinite; vertices on no edge have degree $0$.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) → a multigraph with finitely many edges, loops and parallel edges allowed, loops counted twice in d(v), any vertex type; reason: a finite simple graph is the special case without loops or parallel edges, and Step 3b (p.12) applies the lemma to a graph with parallel edges and self-loops
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Appendix C.1, Lemma 28 (Hakimi, 1965), p.30

import Mathlib
import Definitions.Def_ContPatrol_Multigraph

namespace MalleableSched.Supplement

/-- **Lemma 28 (Hakimi, 1965: an orientation with in-degree at least half the degree).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs under
Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Appendix C.1, Lemma 28, p.30:
"Let G = (V, E) be an undirected graph. For v ∈ V, let d(v) be the degree of node v in G. There is
an orientation of G such that the in-degree of each node v ∈ V is at least ⌊d(v)/2⌋."

**Formalization Note.** `G` is a finite multigraph (the published `ContPatrol.Multigraph`):
finitely many edges `E`, each with two ends `src e`, `tgt e`; loops and parallel edges are allowed
and the vertex type `V` is arbitrary (vertices outside every edge have degree `0`). The degree
`G.deg v` counts a loop twice. An orientation picks, for each edge `e`, one of its two darts
`(e, o e)`; its head is `G.head (e, o e)` (`tgt e` if `o e`, else `src e`), and the in-degree of
`v` is the number of edges whose head is `v`. `⌊d(v)/2⌋` is natural-number division. A simple graph
is the case without loops or parallel edges. -/
theorem lemma_28 {V E : Type} [Fintype E] [DecidableEq V] (G : ContPatrol.Multigraph V E) :
    ∃ o : E → Bool, ∀ v : V,
      G.deg v / 2 ≤ (Finset.univ.filter (fun e => G.head (e, o e) = v)).card := by sorry

end MalleableSched.Supplement
