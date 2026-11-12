-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_13
-- name    : MinCostArbPacking.Main.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:32.009731+00:00
-- url     : https://prove2.me/theorems/f34fd322-9f7a-4aa6-8c76-ed9cd7210ee6
-- title:
--   Lemma 4.13 — path correspondence between $D$ and $D_{\mathrm{fine}}$
-- statement:
--   **Lemma 4.13 (Path correspondence between $D$ and $D_{\mathrm{fine}}$).** Fix a forest decomposition of $I$.
--
--   1. Every simple $u^\star$-to-$z$ path $P_{\mathrm{fine}}$ in $D_{\mathrm{fine}}$ projects to an augmenting path $P$ from $u$ in $D$ with $w(P_{\mathrm{fine}})=\ell(P)$ and $q(P_{\mathrm{fine}})=q(P)$.
--   2. Conversely, every augmenting path from $u$ with no free element before its last one lifts to a $u^\star$-to-$z$ walk in $D_{\mathrm{fine}}$ with the same cost and exchange count.
--   3. If $I$ is extreme, then $D_{\mathrm{fine}}$ has no negative cycle.
--
--   This lets shortest augmenting paths be found in a graph built from forest swaps.
--
--   Differences from the source:
--   - generalization: the arborescence-packing setting of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ cheapest for its indegree vector, no arc of $I$ into $r$, indegree $\le k$) → an arbitrary finite multigraph and any $\mathcal G^k$-independent $I$ with a forest decomposition (extremality assumed only in part (c), as in the source); reason: the proofs use only the forest decomposition (and extremality where stated); a loop has no forest swaps and is never free, an arc entering $r$ is an ordinary element; the reduced graph with the §4.2 invariants is a special case
--   - reading: "lifts to a walk" → a walk whose projection is the given path; reason: the lift described in the proof
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.3.1, p.16, Lemma 4.13

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_SearchGraph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.13 (Path correspondence between `D` and `D_fine`), p.16:
(a) every simple `u⋆`-to-`z` path in `D_fine` projects to an augmenting path `P` from `u` in `D`
with `w = ℓ(P)` and `q = q(P)`;
(b) conversely, every augmenting path from `u` with no free element before its last one lifts to a
`u⋆`-to-`z` walk in `D_fine` with the same cost and exchange count;
(c) if `I` is extreme, `D_fine` has no negative cycle. -/
theorem lemma_4_13 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (c : E → ℝ) (I : Finset E)
    (F : Fin k → Finset E) (hF : G.ForestDecomp k I F) :
    (∀ u as, IsSimpleWalk (G.fineSrc) (G.fineTgt) (G.fineValid k I F) as (.hd u) .sink →
      G.AugFrom k I u (Digraph.projFine as) ∧
        pathCost c I (Digraph.projFine as) = walkWeight (Digraph.fineW c) as ∧
        exchCount I (Digraph.projFine as) = walkQ Digraph.fineQ as) ∧
    (∀ u P, G.AugFrom k I u P → (∀ x ∈ P.dropLast, ¬ G.Free k I x) →
      ∃ as, IsWalk (G.fineSrc) (G.fineTgt) (G.fineValid k I F) as (.hd u) .sink ∧
        Digraph.projFine as = P ∧ walkWeight (Digraph.fineW c) as = pathCost c I P ∧
        walkQ Digraph.fineQ as = exchCount I P) ∧
    (ExtremeP (G.IndepK k) G.head c I →
      ¬ HasNegCycle (G.fineSrc) (G.fineTgt) (G.fineValid k I F) (Digraph.fineW (k := k) c)) := by sorry

end MinCostArbPacking.Main
