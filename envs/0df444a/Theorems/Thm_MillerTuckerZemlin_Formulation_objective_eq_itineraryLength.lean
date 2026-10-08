-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_objective_eq_itineraryLength
-- name    : MillerTuckerZemlin.Formulation.objective_eq_itineraryLength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:24.962901+00:00
-- url     : https://prove2.me/theorems/02fd6b35-c2e1-4464-a7fa-8629271b1e83
-- title:
--   Proof of the equivalence, p. 327 — under the correspondence the objective of (2) is the distance travelled in (1)
-- statement:
--   Let $I$ be a legitimate itinerary of problem (1) of Miller, Tucker and Zemlin with at most $p$ cities per tour, let $a_{ij}(I)$ be the number of times $I$ travels from city $i$ to city $j$, and let $d_{ij}\in\mathbb R$ ($0\le i,j\le n$) be arbitrary distances. Then
--
--   $$
--   \sum\sum_{0\le i\ne j\le n} d_{ij}\,a_{ij}(I)\;=\;\sum_{(i,j)\ \text{travelled by } I} d_{ij},
--   $$
--
--   the right-hand side summing over all arcs of all tours of $I$ with multiplicity. That is, under the correspondence $x=a(I)$ the form minimized in (2) is the total distance travelled by the salesman in (1).
--
--   **Formalization Note** No sign, symmetry or triangle condition is placed on $d$, as on the page. The diagonal $d_{ii}$ appears on neither side: a legitimate itinerary never travels an arc $(i,i)$.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), p. 327, proof of the equivalence, "Under this correspondence the form to be minimized in (2) is the total distance to be traveled by the salesman in (1)"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem objective_eq_itineraryLength (n p : ℕ) (d : Fin (n + 1) → Fin (n + 1) → ℝ)
    (I : Itinerary n) (hI : IsItinerary n p I) :
    objective d (arcCount I) = itineraryLength d I := by sorry

end MillerTuckerZemlin.Formulation
