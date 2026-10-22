-- Prove2me | Theorems.Thm_LPCommunity_MinBisect_R_le_two_t_dOut
-- name    : LPCommunity.MinBisect.R_le_two_t_dOut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:52.5233+00:00
-- url     : https://prove2.me/theorems/c8d27c51-accf-4953-848a-2b193dceaf63
-- title:
--   §2.1, p. 5, proof of Theorem 1 — by definition of d_out, |R| ≤ 2t d_out
-- statement:
--   Let $G$ be a graph on $V=\{1,\dots,n\}$ with a planted bisection $V_1,V_2$ and let $\tilde V_1,\tilde V_2$ be any bisection of $V$. Put $U_1 = V_1\cap\tilde V_1$, $t = |U_1|$, $U_2 = V_2\cap\tilde V_2$, $W_1 = V_1\cap\tilde V_2$, $W_2 = V_2\cap \tilde V_1$, and let $R = R_1\cup R_2$ where $R_1$ is the set of edges with one endnode in $U_1$ and one in $W_2$ and $R_2$ the set of edges with one endnode in $W_1$ and one in $U_2$. Then
--   $$|R| \le 2t\, d_{\mathrm{out}},$$
--   where $d_{\mathrm{out}}$ is the maximum number of neighbours a vertex has on the other side of the planted bisection.
--
--   Every edge of $R$ crosses the planted bisection and has an endnode in $U_1$ or in $U_2$, and $|U_2| = |U_1| = t$ for any two bisections. This is the upper bound on $|R|$ in the proof of Theorem 1.
--
--   **Formalization Note** $\tilde V_1$ is the bisection `W`; $t$ is `(V1 ∩ W).card`. No optimality of `W` is assumed.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, §2.1, p. 5, proof of Theorem 1 (by definition of d_out, |R1| ≤ t d_out and |R2| ≤ t d_out, thus |R| ≤ 2t d_out)

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

namespace LPCommunity.MinBisect

theorem R_le_two_t_dOut {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W) :
    Rcard G V1 W ≤ 2 * (V1 ∩ W).card * dOut G V1 := by sorry

end LPCommunity.MinBisect
