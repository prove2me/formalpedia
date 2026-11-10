-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_6_7
-- name    : LoadBalMatch.Main.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:12.016341+00:00
-- url     : https://prove2.me/theorems/b680ea87-4ac5-4b29-b134-f5a1b80b3751
-- title:
--   Lemma 6.7 ([LP86], Thm 3.2.1) — the Gallai–Edmonds structure theorem
-- statement:
--   Let $H$ be a graph on the finite set $V$ with Gallai–Edmonds decomposition $(D,A,C)$: $D$ is the set of vertices missed by some maximum matching, $A=N_H(D)\setminus D$, $C=V\setminus(D\cup A)$; $D_1,\dots,D_r$ are the connected components of $H[D]$. Then:
--
--   1. Every component $D_i$ induces a **factor-critical** graph: $|D_i|$ is odd and $H[D_i\setminus\{v\}]$ has a perfect matching for every $v\in D_i$; in particular every $D_i$ has a near-perfect matching (covering all but one vertex).
--   2. $H[C]$ has a perfect matching.
--   3. Every maximum matching $M$ of $H$ consists exactly of: a near-perfect matching of each $H[D_i]$ (its edges inside $D_i$ cover all of $D_i$ but one vertex), a perfect matching of $H[C]$ (its edges inside $C$ cover $C$), and one edge from each vertex of $A$ to $D$, the edges at distinct vertices of $A$ going to distinct components $D_i$:
--   $$M=\bigcup_i M[D_i]\ \cup\ M[C]\ \cup\ \{a\,d_a : a\in A\},\qquad d_a\in D,\ \ a\neq a'\Rightarrow d_a,d_{a'} \text{ in different } D_i.$$
--
--   This classical theorem of Gallai and Edmonds (Lovász–Plummer, *Matching Theory*, Theorem 3.2.1) is the structural input of §6–§8.
--
--   Differences from the source:
--   - reading: every maximum matching consists of a near-perfect matching of each component of H[D], a perfect matching in H[C] and edges from all vertices in A to distinct connected components of H[D] → for every maximum matching M: the edges of M inside each D_i cover D_i except one vertex; the edges of M inside C cover C; every a ∈ A is matched by M to some d ∈ D; two distinct A-vertices are matched into different components; and every edge of M is inside some D_i, inside C, or an A–D edge; reason: the literal content of 'consists of' (an equality of edge sets)
--   - encoding: the components D_1, …, D_r of H[D] → the finite set dComps H of components, SameDComp for 'same component'; reason: Lean convention; same objects
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 28, Lemma 6.7

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds

namespace LoadBalMatch.Main

theorem lemma_6_7 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) :
    (∀ S ∈ dComps H, IsFactorCritical H S ∧
      ∃ v ∈ S, ∃ M, IsPerfectMatchingOf H M (↑S \ {v})) ∧
    (∃ M, IsPerfectMatchingOf H M (gC H)) ∧
    ∀ M, IsMaximumMatching H M →
      (∀ S ∈ dComps H, ∃ v ∈ S, IsPerfectMatchingOf H (restrictEdges M ↑S) (↑S \ {v})) ∧
      IsPerfectMatchingOf H (restrictEdges M (gC H)) (gC H) ∧
      (∀ a ∈ gA H, ∃ d ∈ gD H, s(a, d) ∈ M) ∧
      (∀ a a' d d', a ∈ gA H → a' ∈ gA H → d ∈ gD H → d' ∈ gD H →
        s(a, d) ∈ M → s(a', d') ∈ M → a ≠ a' → ¬ SameDComp H d d') ∧
      ∀ e ∈ M, (∃ S ∈ dComps H, ∀ v ∈ e, v ∈ S) ∨ (∀ v ∈ e, v ∈ gC H) ∨
        ∃ a ∈ gA H, ∃ d ∈ gD H, e = s(a, d) := by sorry

end LoadBalMatch.Main
