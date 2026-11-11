-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_13_2
-- name    : MinDegST.AddOne.lemma_13_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:16.808162+00:00
-- url     : https://prove2.me/theorems/db5cffeb-6116-4c6f-9f7e-fdee610d3bd3
-- title:
--   Lemma 13.2 — a feasible forest with exactly one fewer component in Õ(m) time
-- statement:
--   Let $G$ be a connected graph with $n$ nodes and $m$ edges, $k<n$ a threshold for which $G$ has a spanning tree of maximum degree at most $k$, and $F$ a forest of $G$ of maximum degree at most $k+1$ with $f\ge 2$ components. One deterministic word-RAM program and constants $K>0$, $c$ do the following on every such input $(G,k,F)$: halt within
--   $$K\cdot m\cdot(\log_2(n+2))^c+K$$
--   steps and output a forest $F'$ of $G$ of maximum degree at most $k+1$ with exactly $f-1$ components.
--
--   Cited from [BFW26, Lemma 3.1]; it finishes the algorithm of Theorem 1.1 once fewer than $\lceil\sqrt n\rceil$ components remain.
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k < n for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: Õ(m) (polylog factors in n hidden) → ∃ K > 0, c ∈ ℕ: cost ≤ K·m·(log₂(n + 2))^c + K; reason: explicit constants for the asymptotic notation; the additive K covers tiny inputs
--   - encoding: given a feasible forest (of the input graph G); computes a feasible forest → input [n, m, G's edge list, k, |E(F)|, F's edge list] (edges in any order and orientation); output F''s edge list, each edge once; reason: a concrete input/output layout for the RAM; every order is handled
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 35, Lemma 13.2

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine

namespace MinDegST.AddOne

/-- **Lemma 13.2** (threshold form). One deterministic word-RAM program and constants `K > 0`, `c`
such that: for every connected simple graph `G` on `Fin n` (edge list `es`, `m = |es|`), every
threshold `k < n` for which `G` has a spanning tree of maximum degree `≤ k`, and every forest `F` of
`G` with maximum degree `≤ k + 1` and `f ≥ 2` components (edge list `fs`), on input
`(es, k, fs)` the program halts within `K · m · (log₂(n + 2))^c + K` steps and outputs the edges of a
forest `F'` of `G` of maximum degree `≤ k + 1` with exactly one fewer component. -/
theorem lemma_13_2 :
    ∃ (P : CongruencyTU.Program) (width : ℕ) (K : ℝ) (c : ℕ), Deterministic P ∧ 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) (k : ℕ)
        (F : SimpleGraph (Fin n)) (fs : List (Fin n × Fin n)),
        G.Connected → IsEdgeListOf G es → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → IsEdgeListOf F fs → 2 ≤ numComponents F →
          WordBounded P (encForestInput n es k fs) width (n + es.length) ∧
          HaltsWithin P (encForestInput n es k fs)
            (K * (es.length : ℝ) * (Real.logb 2 ((n : ℝ) + 2)) ^ c + K)
            (fun out => ∃ F' : SimpleGraph (Fin n), EncodesEdges out F' ∧
              IsForestOf G F' ∧ Feasible k F' ∧ numComponents F' + 1 = numComponents F) := by sorry

end MinDegST.AddOne
