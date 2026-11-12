-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_14
-- name    : MinCostArbPacking.Main.lemma_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:36.851971+00:00
-- url     : https://prove2.me/theorems/46b4ad0d-4b11-4eec-a16b-bd8ebd2cc27f
-- title:
--   Lemma 4.14 — search in the compressed graph (full and cyclic scans)
-- statement:
--   **Lemma 4.14 (Search in the compressed graph).** Fix a forest decomposition of $I$ and a rooting of every forest. The statements of Lemma 4.13 hold for $D_{\mathrm{cmp}}$ as well: simple $u^\star$-to-$z$ paths project to augmenting paths with the same cost and exchange count, augmenting paths without a nonterminal free element lift, and $D_{\mathrm{cmp}}$ has no negative cycle when $I$ is extreme. If $I$ is extreme, the distance from each $v^\star$ to $z$ equals
--
--   $$d_v=\min\{\ell(P): P \text{ an augmenting path from } v \text{ in } D\}.$$
--
--   Both the graph with all forest scans (p.17) and the cyclic-scan graph (pp.18–19, via Lemma B.1) are covered.
--
--   Differences from the source:
--   - generalization: the arborescence-packing setting of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ cheapest for its indegree vector, no arc of $I$ into $r$, indegree $\le k$) → an arbitrary finite multigraph and any $\mathcal G^k$-independent $I$ with a forest decomposition (extremality assumed only where the source states it); reason: the proofs use only the forest decomposition (and extremality where stated); a loop has no forest swaps and is never free, an arc entering $r$ is an ordinary element; the reduced graph with the §4.2 invariants is a special case
--   - reading: Lemma 4.14 for $D_{\mathrm{cmp}}$, asserted on p.19 to remain valid for the cyclic restriction → both scan policies, as one statement for every policy; reason: the source asserts both and Lemmas 5.3–5.4 use the cyclic one
--   - encoding: "root every component of each forest" → every valid rooting `ρ`; reason: the source's choice of roots is arbitrary
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.3.2, p.18, Lemma 4.14, and p.19 (cyclic scans)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_SearchGraph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.14 (Search in the compressed graph), p.18, for `D_cmp` built with all forest scans
(p.17) and for the cyclic-scan `D_cmp` (p.18–19), for every rooting of the forests: the statements
(a)–(c) of Lemma 4.13 hold for `D_cmp`, and if `I` is extreme the distance from each `v⋆` to `z`
equals the minimum cost of an augmenting path from `v` in `D`. -/
theorem lemma_4_14 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (c : E → ℝ) (I : Finset E)
    (F : Fin k → Finset E) (hF : G.ForestDecomp k I F) (ρ : Fin k → V → Option E)
    (hρ : ∀ i, G.IsRooting (F i) (ρ i)) (pol : Digraph.ScanPolicy) :
    (∀ u as, IsSimpleWalk (G.cmpSrc) (G.cmpTgt ρ) (G.cmpValid k pol I F ρ) as (.hd u) .sink →
      G.AugFrom k I u (Digraph.projCmp as) ∧
        pathCost c I (Digraph.projCmp as) = walkWeight (Digraph.cmpW c) as ∧
        exchCount I (Digraph.projCmp as) = walkQ Digraph.cmpQ as) ∧
    (∀ u P, G.AugFrom k I u P → (∀ x ∈ P.dropLast, ¬ G.Free k I x) →
      ∃ as, IsWalk (G.cmpSrc) (G.cmpTgt ρ) (G.cmpValid k pol I F ρ) as (.hd u) .sink ∧
        Digraph.projCmp as = P ∧ walkWeight (Digraph.cmpW c) as = pathCost c I P ∧
        walkQ Digraph.cmpQ as = exchCount I P) ∧
    (ExtremeP (G.IndepK k) G.head c I →
      ¬ HasNegCycle (G.cmpSrc) (G.cmpTgt ρ) (G.cmpValid k pol I F ρ) (Digraph.cmpW c)) ∧
    (ExtremeP (G.IndepK k) G.head c I → ∀ v,
      walkDist (G.cmpSrc) (G.cmpTgt ρ) (G.cmpValid k pol I F ρ) (Digraph.cmpW c) (.hd v) .sink =
        G.dCost k c I v) := by sorry

end MinCostArbPacking.Main
