-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_itinerary_tourPosition_feasible
-- name    : MillerTuckerZemlin.Formulation.itinerary_tourPosition_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:50.407155+00:00
-- url     : https://prove2.me/theorems/a6004616-8033-4596-8e4b-5dd3e8d083b1
-- title:
--   Proof of the equivalence, p. 328 — the converse: u_i = position of city i in its tour makes an itinerary feasible for (2)
-- statement:
--   Let $I$ be a legitimate itinerary of problem (1) of Miller, Tucker and Zemlin with at most $p$ cities per tour, and let $a_{ij}(I)$ be the number of times $I$ travels from city $i$ to city $j$. For each city $i\ne 0$ let $u_i=j$ when $i$ is the $j$-th city visited in the tour which includes $i$. Then
--
--   $$
--   (x,u)=(a(I),u)\ \text{is feasible for (2)},\qquad 1\le u_i\le p\quad (i=1,\dots,n).
--   $$
--
--   This is the converse half of the equivalence: every legitimate itinerary yields a feasible solution of (2), with the $u_i$ non-negative integers ("it is permissible to restrict the $u_i$ to be non-negative integers as well", p. 327).
--
--   **Formalization Note** The $u_i$ are natural numbers cast to $\mathbb R$; $u_0=0$ and plays no role in (2). The bound $u_i\le p$ is what yields the paper's "and always $u_i-u_j\le p-1$". No hypothesis $p\ge1$ is needed: when $n\ge1$ a legitimate itinerary already forces $p\ge1$.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), p. 328, proof of the equivalence, "Conversely, if the x_ij correspond to a legitimate itinerary"; p. 327, "(We shall see that it is permissible to restrict the u_i to be non-negative integers as well.)"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem itinerary_tourPosition_feasible (n p : ℕ) (I : Itinerary n) (hI : IsItinerary n p I) :
    Feasible n p (arcCount I) (fun i => (tourPosition I i : ℝ)) ∧
      ∀ i : Fin (n + 1), i ≠ 0 → 1 ≤ tourPosition I i ∧ tourPosition I i ≤ p := by sorry

end MillerTuckerZemlin.Formulation
