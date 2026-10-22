-- Prove2me | Theorems.Thm_LPCommunity_MinBisect_two_t_dIn_le_S
-- name    : LPCommunity.MinBisect.two_t_dIn_le_S
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:49.611779+00:00
-- url     : https://prove2.me/theorems/ac9df558-88ef-427f-b7c6-5de6ac325c55
-- title:
--   §2.1, p. 5, proof of Theorem 1 — |S| ≥ 2t(d_in − t + 1)
-- statement:
--   Let $G$ be a graph on $V=\{1,\dots,n\}$ with a planted bisection $V_1,V_2$ and let $\tilde V_1,\tilde V_2$ be any bisection of $V$. Put $U_1 = V_1\cap\tilde V_1$, $t = |U_1|$, $U_2 = V_2\cap\tilde V_2$, $W_1 = V_1\cap\tilde V_2$, $W_2 = V_2\cap \tilde V_1$, and let $S = S_1\cup S_2$ where $S_1$ is the set of edges with one endnode in $U_1$ and one in $W_1$ and $S_2$ the set of edges with one endnode in $U_2$ and one in $W_2$. Then
--   $$|S| \ge 2t\,(d_{\mathrm{in}} - t + 1),$$
--   where $d_{\mathrm{in}}$ is the minimum number of neighbours a vertex has on its own side of the planted bisection.
--
--   Each of the $t$ nodes of $U_1$ has at least $d_{\mathrm{in}}$ neighbours in $V_1$, of which at most $t-1$ lie in $U_1$; symmetrically for $U_2$, which also has $t$ nodes. This is the lower bound on $|S|$ in the proof of Theorem 1. The right-hand side may be negative, in which case the bound is trivial.
--
--   **Formalization Note** The inequality is stated in $\mathbb Z$, so that $d_{\mathrm{in}}-t+1$ is not truncated at $0$. $\tilde V_1$ is the bisection `W`; $t$ is `(V1 ∩ W).card`. No optimality of `W` is assumed.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, §2.1, p. 5, proof of Theorem 1 (|S1| ≥ t(d_in − t + 1), symmetrically |S2| ≥ t(d_in − t + 1), thus |S| ≥ 2t(d_in − t + 1))

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

namespace LPCommunity.MinBisect

theorem two_t_dIn_le_S {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W) :
    2 * ((V1 ∩ W).card : ℤ) * ((dIn G V1 : ℤ) - (V1 ∩ W).card + 1) ≤ (Scard G V1 W : ℤ) := by sorry

end LPCommunity.MinBisect
