-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_4_5
-- name    : LoadBalMatch.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:04.225403+00:00
-- url     : https://prove2.me/theorems/b3308f70-2aac-47f6-b299-b8c4a01ae63c
-- title:
--   Lemma 4.5 — the stabilizing pass leaves a stable subgraph
-- statement:
--   Let $G$ be a graph on the finite vertex set $V$, let $H_0\subseteq G$ be any subgraph, and let $\sigma$ be an edge stream of $G$ (every edge of $G$ exactly once, in any order). Scan $\sigma$ in order and add the current edge $e$ to the current graph $H$ whenever $\mu(H\cup\{e\})>\mu(H)$. Then the final graph $H$ is a **stable** subgraph of $G$ (Definition 2.1):
--   $$\mu(H)=\mu(H\cup\{e\})\qquad\text{for every edge } e \text{ of } G.$$
--
--   This is the guarantee of the second pass of every iteration of Algorithms 1, 3 and 4: the graph on which the next balanced fractional matching is computed cannot be improved by any single edge of $G$.
--
--   Differences from the source:
--   - generalization: H is the subgraph at the end of Line (2b) of Algorithm 1 (the scan started from the graph built in Line (2a)) → the scan started from any subgraph H₀ ≤ G, over any edge stream σ of G; reason: the proof uses only that the scan visits every edge of G once; Line (2b) of Algorithm 1 and Line (2e) of Algorithms 3 and 4 are instances
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 15, Lemma 4.5

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_Stable

namespace LoadBalMatch.Main

theorem lemma_4_5 {V : Type*} [Fintype V] [DecidableEq V] (G H₀ : SimpleGraph V)
    (σ : List (Sym2 V)) (hH₀ : H₀ ≤ G) (hσ : IsEdgeStream G σ) :
    IsStable G (stabilize H₀ σ) := by sorry

end LoadBalMatch.Main
