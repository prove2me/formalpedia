-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_cfl_locality_gap
-- name    : LocalSearchFL.CFL.cfl_locality_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:25:16.957418+00:00
-- url     : https://prove2.me/theorems/06783027-e123-426c-81c5-ab86ccf1f5d7
-- title:
--   Theorem 5.5 — multi-copy local search for metric capacitated facility location has locality gap at most 4
-- statement:
--   Consider the metric capacitated facility location problem in which several copies of a facility may be opened: $C$ is a nonempty finite set of clients, $F$ a set of facilities, $c$ a distance on $C \cup F$ that is nonnegative, symmetric and satisfies the triangle inequality, and every facility $i$ has an opening cost $f_i \ge 0$ per copy and an integer capacity $u_i > 0$ per copy. A solution opens a multiset of copies and assigns every client to a copy, each copy of $i$ serving at most $u_i$ clients; its cost is the total opening cost plus the total distance from clients to their copies.
--
--   Local search moves either add one copy of a facility $s'$, or close a set $T$ of open copies and open $l \ge 1$ copies of a facility $s'$ with $l u_{s'} \ge |N(T)|$, the number of clients served by $T$. If $X$ is locally optimum for these moves, then for every solution $O$,
--
--   $$\mathrm{cost}(X) \le 4 \cdot \mathrm{cost}(O).$$
--
--   This is Theorem 5.5: the locality gap of this local search procedure is at most 4. It is obtained by adding the service-cost bound of Lemma 5.1 and the facility-cost bound of Lemma 5.3.
--
--   **Formalization Note** The hypothesis that there is at least one client is added: without clients, a single idle copy of a facility with $f = 1$, $u = 1$ is locally optimum (its neighbours cost $2$ and $1$) and has cost $1$, while the solution with no copies has cost $0$. $O$ ranges over all solutions with all feasible assignments, so the bound holds in particular against an optimum. The bound is stated multiplied out, since $\mathrm{cost}(O)$ may be $0$.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 560, Theorem 5.5

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Theorem 5.5**, p. 560: local search for the metric capacitated facility location problem
(with multiple copies of a facility allowed), where each step either adds a copy of a facility
or deletes a subset of the open copies and adds multiple copies of one facility (neighbourhood
(9)), has locality gap at most 4: for every instance with at least one client, every locally
optimum solution `X` and every solution `O`, `cost(X) ≤ 4 · cost(O)`. -/
theorem cfl_locality_gap {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    cost I f X ≤ 4 * cost I f O := by sorry

end LocalSearchFL.CFL
