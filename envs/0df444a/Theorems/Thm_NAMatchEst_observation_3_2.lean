-- Prove2me | Theorems.Thm_NAMatchEst_observation_3_2
-- name    : NAMatchEst.observation_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:11.749639+00:00
-- url     : https://prove2.me/theorems/b300697f-8840-482a-9998-0aefb6718d0a
-- title:
--   Observation 3.2 — vertex covers in the no-case
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$.
--
--   Let $M$ be a maximum matching of $G$ and $C$ the set of its endpoints. Then
--
--   1. $C$ is a vertex cover and $|C|=2\mu(G)$;
--   2. if $\mu(G)<k/(C_0\alpha)$, then $V_1\subseteq C$ and $|V_1|<\dfrac{2k}{C_0\alpha}\le\dfrac{k}{100}$;
--   3. if $S\subseteq V$ and $G[S]$ has maximum degree at most $D$, then $|E(G[S])|\le D\,|C|$.
--
--   The observation is the source of every no-case bound of Section 3: a small matching gives a small vertex cover, which contains every high-degree vertex and covers every bounded-degree induced subgraph with few edges.
--
--   **Formalization Note** A maximum matching is a matching subgraph with $\mu(G)$ edges; $C$ is its vertex set. "$G[S]$ has maximum degree at most $D$" is $|N(v)\cap S|\le D$ for all $v\in S$, with $D\ge0$.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - reading: G[S] has maximum degree at most D → a real D ≥ 0 with |N(v) ∩ S| ≤ D for every v ∈ S; reason: a degree bound is nonnegative; for S = ∅ and D < 0 the clause would be false
--   - generalization: the standing assumption that n is sufficiently large (§3.2, p.19) → every n; reason: the statement is deterministic and holds for all n; it specializes to large n
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Observation 3.2, p.20 (PDF 24)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_V1

namespace NAMatchEst

/-- **Observation 3.2 (Vertex covers in the no-case).** Let `C` be the set of endpoints of a maximum
matching of `G`. Then `C` is a vertex cover and `|C| = 2µ(G)`. If `µ(G) < k/(C₀α)`, then `V₁ ⊆ C`
and `|V₁| < 2k/(C₀α) ⩽ k/100`. Moreover, if `S ⊆ V` and `G[S]` has maximum degree at most `D`,
then `|E(G[S])| ⩽ D|C|`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Observation 3.2, p.20 (PDF 24), under the standing setup of §3.2, p.19 (PDF 23):
`n^{1/3} ⩽ α ⩽ n^{1/2}` and an integer `k` with `α ⩽ k ⩽ n`.

**Formalization Note** A maximum matching is a matching subgraph `M` of `G` whose number of edges
is `µ(G)` (`TuranMatching.Clique.matchingNumber`); its endpoint set is `M.verts`. `E(G[S])` is the
set of edges of `G` with both endpoints in `S`, and "`G[S]` has maximum degree at most `D`" is
`|N(v) ∩ S| ⩽ D` for every `v ∈ S`, with `D ⩾ 0` (a degree bound; without it the clause fails
for `S = ∅`, `D < 0` and a graph with an edge). The source's standing "n sufficiently large" is not assumed. -/
theorem observation_3_2 (n : ℕ) (α : ℝ) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    ∀ (G : AdjList n) (M : G.toGraph.Subgraph), M.IsMatching →
      M.edgeSet.ncard = TuranMatching.Clique.matchingNumber G.toGraph →
      (∀ u v, G.toGraph.Adj u v → u ∈ M.verts ∨ v ∈ M.verts) ∧
      M.verts.ncard = 2 * TuranMatching.Clique.matchingNumber G.toGraph ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (↑(V1 G α k) : Set (Fin n)) ⊆ M.verts ∧ ((V1 G α k).card : ℝ) < 2 * k / (C0 * α) ∧
          2 * (k : ℝ) / (C0 * α) ≤ k / 100) ∧
      ∀ (S : Finset (Fin n)) (D : ℝ), 0 ≤ D → (∀ v ∈ S, (((G.adj v).toFinset ∩ S).card : ℝ) ≤ D) →
        (({e ∈ G.toGraph.edgeSet | ∀ v ∈ e, v ∈ S}.ncard : ℕ) : ℝ) ≤ D * M.verts.ncard := by sorry

end NAMatchEst
