-- Prove2me | Theorems.Thm_LNTopology_Hermetic_lemma_B_4
-- name    : LNTopology.Hermetic.lemma_B_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:44.417291+00:00
-- url     : https://prove2.me/theorems/3012383a-f399-4cd9-8012-56f411fbe20f
-- title:
--   Lemma B.4 — a graph with average degree $2d$ has a subgraph with $\delta(G')>d$
-- statement:
--   Let $G$ be a finite simple graph with vertex set $W$ and let $d>0$ be a real number. If the average degree of $G$ is at least $2d$,
--
--   $$\frac{1}{|W|}\sum_{v\in W}\deg_G(v)\ \ge\ 2d,$$
--
--   then $G$ has a nonempty induced subgraph $G'$ with minimum degree $\delta(G')>d$: there is a nonempty $W'\subseteq W$ such that every $v\in W'$ has more than $d$ neighbours in $W'$.
--
--   This classical fact (Diestel, *Graph Theory*, Prop. 1.2.2) supplies the dense subnetwork to which Lemma B.2 is applied in the proof of Theorem 3.8.
--
--   **Formalization Note** "Average degree $2d$" is read as "at least $2d$", as in the paper's proof ("the average degree is at least $2d$"); this implies the version with equality. The hypothesis $d>0$ is added: for an edgeless graph and $d=0$ no nonempty subgraph has minimum degree $>0$. Theorem 3.8 uses the lemma with $d=\bar d(G)/2>0$. Nonemptiness of $G'$ is part of the conclusion, as in the proof. Subgraphs are induced subgraphs, given by their vertex sets.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 12 (PDF p. 13), Lemma B.4

import Mathlib

namespace LNTopology.Hermetic

/-- Lemma B.4: a finite graph with average degree at least `2d`, `d > 0`, has a nonempty induced
subgraph of minimum degree greater than `d`. -/
theorem lemma_B_4 {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (d : ℝ) (hd : 0 < d)
    (havg : 2 * d ≤ (∑ v, (G.degree v : ℝ)) / (Fintype.card W : ℝ)) :
    ∃ W' : Finset W, W'.Nonempty ∧
      ∀ v ∈ W', d < ((G.neighborFinset v ∩ W').card : ℝ) := by sorry

end LNTopology.Hermetic
