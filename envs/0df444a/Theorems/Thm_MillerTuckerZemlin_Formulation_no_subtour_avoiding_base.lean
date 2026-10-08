-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_no_subtour_avoiding_base
-- name    : MillerTuckerZemlin.Formulation.no_subtour_avoiding_base
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:52.922841+00:00
-- url     : https://prove2.me/theorems/2203c851-08c3-4aa6-9473-ba12c9881527
-- title:
--   Proof of the equivalence, pp. 327–328 — a feasible x has no cycle avoiding city 0 (all tours include city 0)
-- statement:
--   Let $(x,u)$ be feasible for problem (2) of Miller, Tucker and Zemlin, with parameter $p\ge 0$. Then there is no cycle of arcs among the non-base cities: there are no $k\ge 0$ and cities $r_0,\dots,r_k$, all different from $0$, such that
--
--   $$
--   x_{r_0r_1}=x_{r_1r_2}=\cdots=x_{r_{k-1}r_k}=x_{r_kr_0}=1 .
--   $$
--
--   This is the paper's conclusion "Thus all tours include city 0": following the successors $r_1,r_2,\dots$ from an arc out of city $0$ must return to $0$, since the alternative is reaching a repeated city $r_k=r_j$, i.e. a cycle avoiding $0$. The statement here excludes every such cycle of the feasible $x$, which is what makes every arc of $x$ lie on a tour through $0$.
--
--   **Formalization Note** The cycle is a map $r$ from $\mathbb Z/(k+1)$ to the cities, so $r_{k+1}=r_0$. The page argues for the cycle met while following successors from city $0$; its argument uses only that the $r$'s are nonzero and that the arcs carry $x=1$, so the statement is made for every such cycle. The case $k=0$ (a loop) is excluded by $x_{ii}=0$.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), pp. 327–328, proof of the equivalence, "Consider any x_{r_0 r_1} = 1 (r_1 ≠ 0)" … "Thus all tours include city 0"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem no_subtour_avoiding_base (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (k : ℕ) (r : Fin (k + 1) → Fin (n + 1))
    (hr : ∀ i, r i ≠ 0) : ¬ ∀ i : Fin (k + 1), x (r i) (r (i + 1)) = 1 := by sorry

end MillerTuckerZemlin.Formulation
