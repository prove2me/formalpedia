-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_7_6
-- name    : LoadBalMatch.Main.lemma_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:57.466423+00:00
-- url     : https://prove2.me/theorems/7e8b4ed2-c7df-49c9-8a11-88a3cbdde5a3
-- title:
--   Lemma 7.6 — a spanning forest $T$ of $\widehat G_H$ lowers $\eta$ by $\frac12\sum_{uv\in T}(1-x_u)^2\ge\frac14\sum_i(1-x_i)^2$
-- statement:
--   Let $G$ be a graph on the finite set $V$, $H\subseteq G$ a stable subgraph, $x\in P(H)$ a balanced fractional matching on $H$, $(D,A,C)$ the Gallai–Edmonds decomposition of $H$ with components $D_1,\dots,D_r$ of $H[D]$ (on which $x$ takes the constant values $x_i$), and $T$ a spanning forest of the contracted graph $\widehat G_H$ (edges of $G$ between different components). Then there is a (not necessarily balanced) fractional matching $y\in P(H\cup T)$ with
--   $$\eta(x)-\eta(y)\ \ge\ \frac12\sum_{uv\in T}(1-x_u)^2\ \ge\ \frac14\sum_{i:\,E[D_i,D\setminus D_i]\neq\emptyset}(1-x_i)^2,$$
--   where $E[D_i,D\setminus D_i]$ is the set of edges of $G$ from $D_i$ to the rest of $D$. By Lemma 6.9 each term $(1-x_u)^2$ is symmetric in $u$ and $v$ (footnote 6).
--
--   This is the progress guarantee of the spanning-forest step of Algorithms 3 and 4.
--
--   Differences from the source:
--   - reading: E[D_i, D∖D_i] with E the edge set of H (first bullet: H = (V, E)) → the edges of G from D_i to D ∖ D_i (dCompsWithExit G H); reason: obvious typo: with H's edges the set is always empty; the proof and every use read it with G's edges (INSIGHTS I4)
--   - encoding: (1 − x_u)² for uv ∈ T → qWeight x uv = ((1 − x_u)² + (1 − x_v)²)/2; reason: x_u = x_v on every edge of T by Lemma 6.9 (footnote 6), so the values agree
--   - encoding: x_i, the common load on D_i → compLoad (load x) D_i, the average load on D_i; reason: x is constant on D_i (Lemma 6.8 item 2), so the values agree
--   - encoding: T ∈ Ĝ_H a spanning forest on Ĝ_H → IsContractedSpanningForest G H T (edges of G between components; spanning and acyclic in the contracted multigraph); reason: same objects
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 36, Lemma 7.6

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_Stable
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds
import Definitions.Def_LoadBalMatch_Main_Violation

namespace LoadBalMatch.Main

theorem lemma_7_6 {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (hH : IsStable G H) (x : Sym2 V → ℝ) (hx : IsBalanced H x) (T : Finset (Sym2 V))
    (hT : IsContractedSpanningForest G H T) :
    ∃ y : Sym2 V → ℝ, IsFracMatching (addEdges H ↑T) y ∧
      (1 / 2) * ∑ e ∈ T, qWeight x e ≤ eta x - eta y ∧
      (1 / 4) * ∑ S ∈ dCompsWithExit G H, (1 - compLoad (load x) S) ^ 2 ≤
        (1 / 2) * ∑ e ∈ T, qWeight x e := by sorry

end LoadBalMatch.Main
