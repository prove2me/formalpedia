-- Prove2me | Theorems.Thm_HypRecov_lemma_D_2
-- name    : HypRecov.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:21.15764+00:00
-- url     : https://prove2.me/theorems/74f747a1-0586-4e87-8bd5-357fd5ac792a
-- title:
--   Lemma D.2 — preservation of cuts with few incident vertices
-- statement:
--   Let $G$ be a graph on $V$ and $C\subseteq G$ a spanning subgraph such that for every edge $uv$ of $G$ not in $C$ there are $h$ internally vertex-disjoint $u$–$v$ paths in $C$. Then, simultaneously for every $S\subseteq V$,
--   $$b_C(S)<h\ \Longrightarrow\ \delta_C(S)=\delta_G(S)\ \text{and}\ b_C(S)=b_G(S),$$
--   where $\delta_J(S)$ is the edge boundary and $b_J(S)$ the number of vertices incident to it.
--
--   This is how the connectivity certificate of Theorem D.1 preserves every bridge cut of the pair-support graph.
--
--   Differences from the source:
--   - generalization: G the simple pair-support graph of H → any simple graph G on Fin n; reason: the proof uses only C ⊆ G
--   - encoding: δ_C(S), b_C(S), internally vertex-disjoint paths → crossEdges, incident, IntDisjointPaths; reason: Lean convention
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma D.2, p.37 (PDF p.38)

import Mathlib
import Definitions.Def_HypRecov_incident

namespace HypRecov

/-- **Lemma D.2 (Preservation of cuts with few incident vertices).** Zhang, Chen, Shen, *Hypergraph
Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma
D.2, p.37 (PDF p.38): "Let C ⊆ G be a spanning subgraph such that, for every uv ∈ E(G) ∖ E(C), there
are h internally vertex-disjoint u–v paths in C. Then, simultaneously for every S ⊆ V, b_C(S) < h ⟹
δ_C(S) = δ_G(S) and b_C(S) = b_G(S)."

**Formalization Note.** The paper's `G` is the pair-support graph of `H`; the lemma is stated for every
simple graph `G` on `Fin n`. `δ` is the edge boundary `crossEdges`, `b` the number of incident vertices. -/
theorem lemma_D_2 {n : ℕ} (G C : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel C.Adj]
    (hCG : C ≤ G) (h : ℕ)
    (hpaths : ∀ u v : Fin n, G.Adj u v → ¬ C.Adj u v → IntDisjointPaths C u v h)
    (S : Finset (Fin n)) (hb : (incident C S).card < h) :
    crossEdges C S = crossEdges G S ∧ (incident C S).card = (incident G S).card := by sorry

end HypRecov
