-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_6_9
-- name    : LoadBalMatch.Main.lemma_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:59.86942+00:00
-- url     : https://prove2.me/theorems/c45c526f-f517-469f-a811-0f2e05b8eca5
-- title:
--   Lemma 6.9 — on a stable subgraph, a balanced $x$ has equal loads across every edge of $G[D]$
-- statement:
--   Let $G$ be a graph on the finite set $V$ and let $H\subseteq G$ be stable: $\mu(H)=\mu(H\cup\{e\})$ for every edge $e$ of $G$. Let $(D,A,C)$ be the Gallai–Edmonds decomposition of $H$ and $x$ a balanced fractional matching on $H$, with loads $x_v$. Then
--   $$x_u=x_v\qquad\text{for every edge } uv \text{ of } G \text{ with } u,v\in D.$$
--
--   Edges of $G$ between different components of $H[D]$ therefore join vertices of equal load, which is what makes the weight $q$ of §7 well defined and every spanning forest of $\widehat G_H$ equally heavy.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 30, Lemma 6.9

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Stable
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds

namespace LoadBalMatch.Main

theorem lemma_6_9 {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (hH : IsStable G H) (x : Sym2 V → ℝ) (hx : IsBalanced H x) :
    ∀ u v, u ∈ gD H → v ∈ gD H → G.Adj u v → load x u = load x v := by sorry

end LoadBalMatch.Main
