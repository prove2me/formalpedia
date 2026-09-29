-- Prove2me | Theorems.Thm_MetricTSP_tour_vector_held_karp
-- name    : MetricTSP.tour_vector_held_karp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T19:21:17.311736+00:00
-- url     : https://prove2.me/theorems/1c92d72c-ad52-4884-8709-82fe2dbcab98
-- title:
--   Tour incidence vectors are feasible for the subtour LP
-- statement:
--   For $n \ge 3$ cities, the incidence vector of any Hamiltonian tour is a feasible point of the subtour-elimination (Held--Karp) relaxation. Concretely, the vector $x_{uv} = $ (number of steps of the tour traversing the pair $\{u,v\}$) satisfies:
--
--   1. symmetry $x_{uv} = x_{vu}$ and zero diagonal $x_{vv} = 0$;
--   2. $0 \le x_{uv} \le 1$ --- for $n \ge 3$ a Hamiltonian cycle traverses no pair twice;
--   3. degree two at every city: $\sum_u x_{vu} = 2$, since the tour enters and leaves each city exactly once;
--   4. every nontrivial cut is crossed at least twice: for every set $S$ of cities with $\emptyset \ne S \ne V$, $\sum_{u \in S}\sum_{v \notin S} x_{uv} \ge 2$, because a cyclic sequence visiting both sides of the cut must leave $S$ and return to $S$.
--
--   This is the *validity* half of the Held--Karp bound: the subtour-elimination LP is genuinely a relaxation of the traveling salesman problem, since every tour contributes a feasible point.
-- source:
--   G. Dantzig, R. Fulkerson, S. Johnson, Solution of a large-scale traveling-salesman problem, Operations Research 2 (1954) 393-410 (the subtour-elimination constraints, satisfied by every tour); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Section 11.2 (every tour vector is feasible for the subtour LP, so the LP is a relaxation).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector

namespace MetricTSP

theorem tour_vector_held_karp (n : ℕ) (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) :
    IsHeldKarp (tourVec π) := by sorry

end MetricTSP
