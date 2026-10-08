-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_mtz_formulation_equivalent
-- name    : MillerTuckerZemlin.Formulation.mtz_formulation_equivalent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:44.437657+00:00
-- url     : https://prove2.me/theorems/7e2d10b5-759a-4daf-9b0a-341c4d474821
-- title:
--   Equivalence of (1) and (2), pp. 326–328 — the MTZ integer program describes exactly the itineraries with at most p cities per tour
-- statement:
--   Fix $n\ge 0$ cities besides the base city $0$ and a bound $p\ge 1$ on the number of cities per tour. Let problem (1) be the set of legitimate itineraries: lists of tours from city $0$, each tour a nonempty succession of at most $p$ cities other than $0$, visiting each of the cities $1,\dots,n$ exactly once in all. For an itinerary $I$ write $a_{ij}(I)$ for the number of times it travels from city $i$ to city $j$ and $t(I)$ for its number of tours (returns to $0$). Let problem (2) be the integer program with non-negative integers $x_{ij}$ ($0\le i\ne j\le n$) and real $u_1,\dots,u_n$ subject to
--
--   $$
--   \sum_{\substack{i=0\\ i\ne j}}^{n} x_{ij}=1\ (j\ge1),\qquad \sum_{\substack{j=0\\ j\ne i}}^{n} x_{ij}=1\ (i\ge1),\qquad u_i-u_j+p\,x_{ij}\le p-1\ (1\le i\ne j\le n),
--   $$
--
--   with objective $\sum\sum_{i\ne j} d_{ij}x_{ij}$. Then:
--
--   1. if $(x,u)$ is feasible for (2), there is a legitimate itinerary $I$ with $x=a(I)$, and $\sum_{i=1}^n x_{i0}=t(I)$;
--   2. conversely, for every legitimate itinerary $I$ there are non-negative integers $u_1,\dots,u_n$ with $(a(I),u)$ feasible for (2), and $\sum_{i=1}^n a_{i0}(I)=t(I)$;
--   3. for all real distances $d_{ij}$ and every legitimate itinerary $I$, $\sum\sum_{i\ne j}d_{ij}a_{ij}(I)$ is the total distance travelled along $I$.
--
--   This is the paper's claim that (2) "will be shown to be equivalent to (1)", in the form of its "burden of proof": the feasible sets correspond under "the salesman proceeds from city $i$ to city $j$ if and only if $x_{ij}=1$", and the objectives agree. Parts 1 and 2 also cover fixed $t$: adding $\sum_{i=1}^n x_{i0}=t$ to (2) corresponds to itineraries with exactly $t$ tours.
--
--   **Formalization Note** The hypothesis $p\ge 1$ is not on the page; without it the claim is false ($n=1$, $p=0$: $x_{01}=x_{10}=1$ is feasible for (2) but no itinerary exists). The paper's "a feasible solution to (2) has $x_{ij}$ which do define a legitimate itinerary" is read as $x$ being equal to the arc counts of that itinerary; "together with appropriate $u_i$" is made explicit as the existence of natural-number $u_i$ (the paper's remark that the $u_i$ may be taken non-negative integers). Cities are `Fin (n + 1)`, an itinerary is a list of tours (lists of cities), and the absent variables $x_{ii}$ are encoded as $x_{ii}=0$.
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), pp. 326–328, equivalence of (1) and (2) (stated p. 326–327, burden of proof p. 327, proof pp. 327–328)

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem mtz_formulation_equivalent (n p : ℕ) (hp : 1 ≤ p) :
    (∀ (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ), Feasible n p x u →
        ∃ I : Itinerary n, IsItinerary n p I ∧ x = arcCount I ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), x i 0 = I.length) ∧
    (∀ I : Itinerary n, IsItinerary n p I →
        (∃ u : Fin (n + 1) → ℕ, Feasible n p (arcCount I) (fun i => (u i : ℝ))) ∧
          ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))), arcCount I i 0 = I.length) ∧
    (∀ (d : Fin (n + 1) → Fin (n + 1) → ℝ) (I : Itinerary n), IsItinerary n p I →
        objective d (arcCount I) = itineraryLength d I) := by sorry

end MillerTuckerZemlin.Formulation
