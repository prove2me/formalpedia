-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_potential_path_bound
-- name    : MillerTuckerZemlin.Formulation.potential_path_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:27.024422+00:00
-- url     : https://prove2.me/theorems/9f4eb98f-9c91-477c-bdcc-1e7cd5ef6f28
-- title:
--   Proof of the equivalence, p. 328 — along a path of m arcs avoiding city 0 the potentials u rise by at least m
-- statement:
--   Let $(x,u)$ be feasible for problem (2) of Miller, Tucker and Zemlin, with parameter $p\ge 0$. Let $r_0,r_1,\dots,r_m$ ($m\ge 0$) be cities, none equal to the base city $0$, such that $x_{r_kr_{k+1}}=1$ for $k=0,\dots,m-1$. Then
--
--   $$
--   u_{r_0}-u_{r_m}\le -m .
--   $$
--
--   For a single arc ($m=1$) this is the paper's inequality $u_{r_i}-u_{r_{i+1}}\le -1$, obtained from $u_{r_i}-u_{r_{i+1}}+p\,x_{r_ir_{i+1}}\le p-1$; for general $m$ it is the summed form the paper uses twice ("Summing from $i=j$ to $k-1$" and "Then, as before, $u_{r_1}-u_{r_{p+1}}\le -p$"). The $u_i$ thus act as node potentials that strictly increase along every arc between non-base cities.
--
--   **Formalization Note** The path is a map $r$ from $\{0,\dots,m\}$ to the cities. Consecutive cities of the path are automatically distinct, since $x_{ii}=0$ in the encoding of (2). The page states the summed bound as $\le j+1-k$; the exact sum is $j-k$, which is what is stated here ($-m$ for a path of $m$ arcs). No hypothesis $p\ge1$ is needed.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), p. 328, proof of the equivalence, "Since none of the r's are zero we have" and "Summing from i = j to k − 1"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem potential_path_bound (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (m : ℕ) (r : Fin (m + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (hpath : ∀ k : Fin m, x (r k.castSucc) (r k.succ) = 1) :
    u (r 0) - u (r (Fin.last m)) ≤ -(m : ℝ) := by sorry

end MillerTuckerZemlin.Formulation
