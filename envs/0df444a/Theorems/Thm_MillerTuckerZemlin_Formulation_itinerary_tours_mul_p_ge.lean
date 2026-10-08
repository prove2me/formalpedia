-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_itinerary_tours_mul_p_ge
-- name    : MillerTuckerZemlin.Formulation.itinerary_tours_mul_p_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:23.335231+00:00
-- url     : https://prove2.me/theorems/81fd4f5e-d168-4831-98b6-a1dedc55aed9
-- title:
--   Remark, p. 326 — an itinerary with t tours of at most p cities each requires tp ≥ n
-- statement:
--   Let $I$ be a legitimate itinerary of problem (1) of Miller, Tucker and Zemlin: $t$ tours from the base city $0$, together visiting each of the cities $1,\dots,n$ exactly once, each tour visiting at most $p$ cities. Then
--
--   $$
--   tp\ \ge\ n .
--   $$
--
--   This is the paper's remark that, for fixed $t$, problem (1) has a solution only if $tp\ge n$; for $t=1$, $p\ge n$ it is the standard traveling salesman problem.
--
--   **Formalization Note** $t$ is the number of tours of the itinerary, i.e. the length of the list.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), p. 326, remark after (1), "Note that if t is fixed, then for the problem to have a solution we must have tp ≧ n"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem itinerary_tours_mul_p_ge (n p : ℕ) (I : Itinerary n) (hI : IsItinerary n p I) :
    n ≤ I.length * p := by sorry

end MillerTuckerZemlin.Formulation
