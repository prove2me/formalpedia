-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_2_1
-- name    : MatroidSensOracle.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:03.908503+00:00
-- url     : https://prove2.me/theorems/cf31ee31-752c-4350-bf5d-0257b3153a19
-- title:
--   Lemma 2.1: $w\in A$ iff $\lambda_{G+(w,t)}(s,t)=\lambda_G(s,t)+1$, for the nearest min-cut $(A,B)$
-- statement:
--   Let $G$ be a directed multigraph with unit capacities on vertices $V=\{0,\dots,n-1\}$, let $s\ne t$, and let $A$ be the source side of the nearest $(s,t)$-min-cut $\mathrm{NMC}_G(s,t)$. For every vertex $w$,
--   $$w\in A\iff w\ne t\ \text{ and }\ \lambda_{G+(w,t)}(s,t)=\lambda_G(s,t)+1,$$
--   where $G+(w,t)$ is $G$ with one new edge from $w$ to $t$.
--
--   The nearest-min-cut oracle of Theorem 5.5 reports $A$ by testing this condition for every $w$.
--
--   Differences from the source:
--   - reading: G_w := G + (w, t) → G with one new edge (w, t), parallel to an existing one if (w, t) ∈ E; reason: with set union the lemma fails: V = {s, t}, E = {(s, t)} gives A = {s} but λ stays 1
--   - generalization: G a directed graph → G any directed multigraph with unit capacities; reason: the lemma holds for multigraphs; simple graphs are a special case
--   - encoding: C = NMC_G(s, t) with partition (A, B) → A a finite vertex set with IsNearestMinCut G s t A; reason: the nearest min-cut is unique, so the hypothesis names it
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 2.1, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_MatroidSensOracle_CostMultigraph

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Lemma 2.1.** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), p.12
(PDF p.15): "Let C = NMC_G(s, t) with partition (A, B). Then A consists of those w ∈ V \ {t} for which
G_w := G + (w, t) satisfies λ_{G_w}(s, t) = λ_G(s, t) + 1."

**Formalization Note.** `G` is a directed multigraph with unit capacities (`CostMultigraph`, costs
irrelevant). `G + (w, t)` adds a **new** edge `(w, t)` (cost `0`), parallel to an existing one if
`(w, t)` is already an edge: with set union the lemma fails for `V = {s, t}`, `E = {(s, t)}`. `A` is
the source side of the nearest min-cut. -/
theorem lemma_2_1 {n : ℕ} (G : CostMultigraph (Fin n)) (s t : Fin n) (hst : s ≠ t)
    (A : Finset (Fin n)) (hA : G.IsNearestMinCut s t A) (w : Fin n) :
    w ∈ A ↔ w ≠ t ∧ (G.addEdges [(w, t, 0)]).maxFlow s t = G.maxFlow s t + 1 := by sorry

end MatroidSensOracle
