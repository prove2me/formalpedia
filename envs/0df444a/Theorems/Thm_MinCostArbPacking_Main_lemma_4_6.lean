-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_6
-- name    : MinCostArbPacking.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:20.136477+00:00
-- url     : https://prove2.me/theorems/f616632c-ce56-4791-8144-6afd6dd652b7
-- title:
--   Lemma 4.6 — indegree bounds after contraction
-- statement:
--   **Lemma 4.6 (Indegree bounds after contraction).** Assume the standing assumptions of §4.2 and that every deficient tight block $T$ has a proposal $P_T$ from a deficient vertex $u_T\in T$. In the contracted graph with arc set $H=I^{cr}\,\dot\cup\,A$, every vertex has indegree at most $k$, and with $t=|\mathcal T(I)|$,
--
--   $$|I^{cr}|+|A|\le k(t-1).$$
--
--   This lets the forest-packing algorithm of Lemma 3.6 be applied to the contracted graph.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ independent, cheapest for its indegree vector, no arc into $r$, indegree $\le k$) → explicit hypotheses `NoLoopNoRootArc` and `Standing`; reason: the source states them once for the whole section; they are hypotheses of every lemma there
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.2.2, p.12, Lemma 4.6

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.6 (Indegree bounds after contraction), p.12: with proposals in every deficient block,
every vertex of the contracted graph has indegree at most `k` in `H = I^cr ∪̇ A`, and
`|I^cr| + |A| ≤ k(t - 1)` with `t = |𝒯(I)|`. -/
theorem lemma_4_6 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (I : Finset E) (hI : G.Standing k r c I)
    (u : Finset V → V) (P : Finset V → List E) (hP : G.IsProposalSystem k r c I u P) :
    (∀ B : Finset V, (G.contract k I).inDeg (G.crossingPart k I ∪ G.terminals k r I P) B ≤ k) ∧
    (G.crossingPart k I).card + (G.terminals k r I P).card ≤ k * (G.numBlocks k I - 1) := by sorry

end MinCostArbPacking.Main
