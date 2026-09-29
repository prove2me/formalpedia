-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_ufl_locality_gap
-- name    : LocalSearchFL.UFL.ufl_locality_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:18:52.325694+00:00
-- url     : https://prove2.me/theorems/8d641d7d-687f-4311-a82f-27350ecf6b87
-- title:
--   Theorem 4.3: add/drop/swap local search for metric UFL has locality gap at most 3
-- statement:
--   Let $C$ be a finite set of clients and $F$ a finite set of facilities, with a distance on $C \cup F$ that is nonnegative, symmetric and satisfies the triangle inequality, and let $c_{ji}$ be the cost of serving client $j$ by facility $i$. Each facility $i$ has an opening cost $f_i \ge 0$. The cost of a nonempty set $S \subseteq F$ of open facilities is
--   $$\mathrm{cost}(S) = \sum_{i \in S} f_i + \sum_{j \in C} \min_{i \in S} c_{ji}.$$
--   $S$ is locally optimum for the neighbourhood
--   $$\mathcal B(S) = \{S + \{s'\}\} \cup \{S - \{s\} \mid s \in S\} \cup \{S - \{s\} + \{s'\} \mid s \in S\}$$
--   if no neighbour has smaller cost.
--
--   **Theorem 4.3.** If $S$ is locally optimum for $\mathcal B$, then for every nonempty $O \subseteq F$,
--   $$\mathrm{cost}(S) \le 3 \cdot \mathrm{cost}(O).$$
--
--   In words: the local search procedure that adds, drops or swaps one facility at a time has locality gap at most 3 for the metric uncapacitated facility location problem. The bound is tight (§4.3 of the paper).
--
--   **Formalization Note** The locality gap bound is stated as the inequality for every local optimum $S$ and every solution $O$ (not only an optimal one), multiplied out rather than as a ratio. Only nonempty sets are solutions; the drop move is considered only when a facility remains open.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 557, Theorem 4.3

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Theorem 4.3, p. 557: local search for the metric UFL problem with the neighbourhood
`B(S) = {S + {s'}} ∪ {S − {s} | s ∈ S} ∪ {S − {s} + {s'} | s ∈ S}` has locality gap at most 3:
if `S` is locally optimum for `B`, then `cost(S) ≤ 3 · cost(O)` for every solution `O`. -/
theorem ufl_locality_gap {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) :
    uflCost I f S hS ≤ 3 * uflCost I f O hO := by sorry

end LocalSearchFL.UFL
