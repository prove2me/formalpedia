-- Prove2me | Theorems.Thm_LPCommunity_MinBisect_S_le_R_of_optimal
-- name    : LPCommunity.MinBisect.S_le_R_of_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:45.460058+00:00
-- url     : https://prove2.me/theorems/ce8aa1cc-a8fd-4b76-a086-9294cbc82eef
-- title:
--   §2.1, p. 5, proof of Theorem 1 — optimality of the bisection Ṽ1, Ṽ2 implies |S| ≤ |R|
-- statement:
--   Let $G$ be a graph on $V=\{1,\dots,n\}$ with a planted bisection $V_1, V_2$, and let $\tilde V_1,\tilde V_2$ be an optimal solution of the minimum bisection problem, i.e. a bisection whose cost is at most the cost of every bisection of $V$. With $U_1 = V_1\cap\tilde V_1$, $U_2 = V_2\cap\tilde V_2$, $W_1 = V_1\cap\tilde V_2$, $W_2=V_2\cap\tilde V_1$ and the edge sets
--   $R = R_1\cup R_2$ (edges $U_1$–$W_2$ and $W_1$–$U_2$) and $S = S_1\cup S_2$ (edges $U_1$–$W_1$ and $U_2$–$W_2$), we have
--   $$|S| \le |R|.$$
--
--   The edges cut by $\tilde V_1,\tilde V_2$ are $S\cup T$ and those cut by the planted bisection are $R\cup T$, with $T = T_1\cup T_2$ (edges $U_1$–$U_2$ and $W_1$–$W_2$); optimality gives $|S|+|T|\le|R|+|T|$. This is the first of the three inequalities that combine into Theorem 1.
--
--   **Formalization Note** $\tilde V_1$ is the `Finset` `W` and $\tilde V_2$ = `Wᶜ`; optimality is stated as `cutCost G W ≤ cutCost G S` for every bisection `S`. The paper's additional normalizations ($|U_1|\le n/4$, $U_1\neq\emptyset$) are not needed for this step and are not assumed.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, §2.1, p. 5, proof of Theorem 1 (the optimality of the bisection Ṽ1, Ṽ2 implies |S| ≤ |R|)

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

namespace LPCommunity.MinBisect

theorem S_le_R_of_optimal {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n))
    (hV1 : IsBisection n V1) (hW : IsBisection n W)
    (hopt : ∀ S : Finset (Fin n), IsBisection n S → cutCost G W ≤ cutCost G S) :
    Scard G V1 W ≤ Rcard G V1 W := by sorry

end LPCommunity.MinBisect
