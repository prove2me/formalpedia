-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_7_11
-- name    : LoadBalMatch.Main.lemma_7_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:34:06.384413+00:00
-- url     : https://prove2.me/theorems/98fa8910-fba7-47c3-861c-ca5fd91e11ed
-- title:
--   Lemma 7.11 — $\Phi\le 2\sum_e\sqrt{w(e)}x^\star_e+2\sum_i(1-x_i)\min\{\sum_{E[D_i,D\setminus D_i]}x^\star_e,1\}$
-- statement:
--   Let $G$ be a graph on the finite set $V$ with edge set $E$, $x^\star$ a balanced fractional matching of $G$, $H\subseteq G$ a stable subgraph, and $x$ a balanced fractional matching on $H$, with levels in $H$; let $(D,A,C)$ be the Gallai–Edmonds decomposition of $H$, $D_1,\dots,D_r$ the components of $H[D]$, $x_i$ the common load on $D_i$, and $w$ the weight of eq. (36) for $H$ and $x$. Then
--   $$\eta(x)-\eta(G)\ \le\ 2\sum_{e\in E}\sqrt{w(e)}\,x^\star_e\;+\;2\sum_{i}(1-x_i)\min\Big\{\sum_{e\in E[D_i,D\setminus D_i]}x^\star_e,\ 1\Big\},$$
--   where $E[D_i,D\setminus D_i]$ is the set of edges of $G$ from $D_i$ to the rest of $D$.
--
--   The paper states this for every iteration $t\ge1$ of Algorithm 3 ($x=x^{(t)}$ on $H^{(t)}$, $\Phi_t$ on the left): either a heavy external matching or many components with outgoing edges must exist.
--
--   Differences from the source:
--   - generalization: every t ≥ 1 of Algorithm 3: x = x^(t) on H^(t) = supp(x^(t)) → any stable H ≤ G and any balanced x on H; reason: H^(t) is stable (it lies inside the stable graph of the last pass with the same µ) and x^(t) is balanced on it; the proof uses only Lemmas 6.3, 6.7, 6.8
--   - encoding: Σ_{e∈E} → the sum over all pairs Sym2 V; reason: x⋆ vanishes off E, so the sums agree
--   - encoding: x_i, the common load on D_i → compLoad (load x) D_i, the average load on D_i; reason: x is constant on D_i (Lemma 6.8 item 2)
--   - encoding: Φ_t = η(x^(t)) − η⋆ → eta x − etaOpt G; reason: etaOpt G is the attained minimum
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 40, Lemma 7.11

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Stable
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds
import Definitions.Def_LoadBalMatch_Main_Violation

namespace LoadBalMatch.Main

theorem lemma_7_11 {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    (hH : IsStable G H) (x : Sym2 V → ℝ) (hx : IsBalanced H x) (xs : Sym2 V → ℝ)
    (hxs : IsBalanced G xs) :
    eta x - etaOpt G ≤
      2 * ∑ e, Real.sqrt (extWeight H x e) * xs e +
      2 * ∑ S ∈ dComps H, (1 - compLoad (load x) S) * min (cut xs ↑S (gD H \ ↑S)) 1 := by sorry

end LoadBalMatch.Main
