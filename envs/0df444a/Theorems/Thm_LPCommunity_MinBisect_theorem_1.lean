-- Prove2me | Theorems.Thm_LPCommunity_MinBisect_theorem_1
-- name    : LPCommunity.MinBisect.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:57.922199+00:00
-- url     : https://prove2.me/theorems/2413ddc3-65af-40a8-bd0c-54ca6b581651
-- title:
--   Theorem 1, p. 4 — if d_in − d_out > n/4 − 1, the minimum bisection problem recovers the planted bisection
-- statement:
--   Let $G=(V,E)$ be a graph on $V=\{1,\dots,n\}$ with a planted bisection $V_1,V_2$ ($|V_1|=|V_2|=n/2$). Let $d_{\mathrm{in}}$ be the minimum degree of the nodes of $G[V_1]\cup G[V_2]$ and $d_{\mathrm{out}}$ the maximum degree of the nodes of the bipartite graph $G_0$ of edges between $V_1$ and $V_2$. If
--   $$d_{\mathrm{in}} - d_{\mathrm{out}} > \frac{n}{4} - 1,$$
--   then the minimum bisection problem recovers the planted bisection: $\{V_1,V_2\}$ is the unique bisection of $V$ of minimum cost.
--
--   The condition involves only the worst-case degree inside and across the communities, with no randomness. It is tight: by Theorem 2 of the paper, for every $n$ divisible by eight and every admissible pair with $d_{\mathrm{in}} - d_{\mathrm{out}} \le n/4-1$ there are graphs on which recovery fails. Section 3 of the paper compares it with the condition $d_{\mathrm{in}} - d_{\mathrm{out}}\ge n/4$ under which the metric LP relaxation recovers the planted bisection.
--
--   **Formalization Note** The vertex set is `Fin n`. $d_{\mathrm{in}}$ and $d_{\mathrm{out}}$ are the defined `dIn`, `dOut`, and the hypothesis is compared in $\mathbb R$ (real division $n/4$, no truncated subtraction). "Recovers" means: every bisection `S` with `cutCost G S ≤ cutCost G V1` equals `V1` or `V1ᶜ`. At $n=0$ the statement holds trivially (the only bisection is $\emptyset$).
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 4, Theorem 1

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

namespace LPCommunity.MinBisect

theorem theorem_1 {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) (hV1 : IsBisection n V1)
    (h : (dIn G V1 : ℝ) - (dOut G V1 : ℝ) > (n : ℝ) / 4 - 1) :
    MinBisectRecovers G V1 := by sorry

end LPCommunity.MinBisect
