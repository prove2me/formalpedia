-- Prove2me | Theorems.Thm_LNTopology_Hermetic_lemma_B_3
-- name    : LNTopology.Hermetic.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:19.646744+00:00
-- url     : https://prove2.me/theorems/7c6483b8-4483-4ec5-a9ae-2998de5a1c3e
-- title:
--   Lemma B.3 — the peeling procedure finds the largest induced subgraph with minimum degree above $t$
-- statement:
--   Let $G$ be a finite simple graph with vertex set $W$, let $t$ be a real number, and let $\mathrm{peel}(G,t)\subseteq W$ be the output of the peeling procedure of Lemma B.3, which repeatedly deletes every vertex having at most $t$ neighbours among the remaining vertices. Then
--
--   1. every $v\in\mathrm{peel}(G,t)$ has more than $t$ neighbours in $\mathrm{peel}(G,t)$; and
--   2. every $W'\subseteq W$ in which each vertex has more than $t$ neighbours in $W'$ is contained in $\mathrm{peel}(G,t)$.
--
--   Consequently the procedure returns a nonempty induced subgraph $H$ with $\delta(H)>t$ if one exists, and the empty graph otherwise. With $t=g_+^{-1}(2\,\mathrm{disc}(G))$ this is the algorithm of Lemma B.3, which finds the subnetwork to which Lemma B.2 is applied.
--
--   **Formalization Note** The statement of Lemma B.3 promises a subgraph with $\delta(H)\ge t$, while the procedure of its proof deletes vertices of degree $\le t$ and therefore finds $\delta(H)>t$; for integer $t$ the two differ (a $t$-regular graph). The procedure as written in the proof is formalized; the proof of Theorem 3.8 needs only this strict version. The existence of "an algorithm" (trivial classically) and the $O(V+E)$ running time are not formalized. The threshold is an arbitrary real $t$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 12 (PDF p. 13), Lemma B.3 and its proof

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Peel

namespace LNTopology.Hermetic

/-- Lemma B.3, correctness of the peeling procedure of its proof: repeatedly deleting every vertex
with at most `t` neighbours among the remaining vertices yields a set in which every vertex has
more than `t` neighbours, and which contains every vertex set with that property. -/
theorem lemma_B_3 {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (t : ℝ) :
    (∀ v ∈ peel G t, t < ((G.neighborFinset v ∩ peel G t).card : ℝ)) ∧
      ∀ W' : Finset W, (∀ v ∈ W', t < ((G.neighborFinset v ∩ W').card : ℝ)) →
        W' ⊆ peel G t := by sorry

end LNTopology.Hermetic
