-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_no_tour_longer_than_p
-- name    : MillerTuckerZemlin.Formulation.no_tour_longer_than_p
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:57.680367+00:00
-- url     : https://prove2.me/theorems/c777fe20-73a2-4a17-a1a7-f954ca70b6a6
-- title:
--   Proof of the equivalence, p. 328 — no tour of a feasible x visits more than p cities
-- statement:
--   Let $p\ge 1$ and let $(x,u)$ be feasible for problem (2) of Miller, Tucker and Zemlin. Then no tour of $x$ visits more than $p$ cities: there are no cities $r_1,\dots,r_{p+1}$, all different from the base city $0$, with
--
--   $$
--   x_{0r_1}=x_{r_1r_2}=\cdots=x_{r_pr_{p+1}}=1 .
--   $$
--
--   Together with the absence of subtours avoiding $0$, this is the half of the equivalence that shows a feasible solution of (2) describes an itinerary of (1) with at most $p$ cities per tour.
--
--   **Formalization Note** The cities $r_1,\dots,r_{p+1}$ are a map from $\{0,\dots,p\}$ to the cities (index shifted down by one). The hypothesis $p\ge1$ is not on the page: for $p=0$ the claim is false (with $n=1$, $x_{01}=x_{10}=1$ is feasible, there being no $u$-constraint, and $x_{01}=1$ is a tour of $1>0$ cities). The paper's step $u_{r_{p+1}}-u_{r_1}+p\,x_{r_{p+1}r_1}\le p-1$ needs $r_{p+1}\ne r_1$, which the paper leaves implicit.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), p. 328, proof of the equivalence, "It remains to observe that no tour is of length greater than p"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem no_tour_longer_than_p (n p : ℕ) (hp : 1 ≤ p) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (r : Fin (p + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (h0 : x 0 (r 0) = 1) :
    ¬ ∀ k : Fin p, x (r k.castSucc) (r k.succ) = 1 := by sorry

end MillerTuckerZemlin.Formulation
