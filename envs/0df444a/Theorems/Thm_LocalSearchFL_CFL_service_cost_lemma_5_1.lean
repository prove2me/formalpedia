-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_service_cost_lemma_5_1
-- name    : LocalSearchFL.CFL.service_cost_lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:21:44.937701+00:00
-- url     : https://prove2.me/theorems/f8581ef4-3cac-41db-ade8-f6f3ca806a4a
-- title:
--   Lemma 5.1 — service cost of a CFL local optimum is at most cost_f(O) + cost_s(O)
-- statement:
--   Let $C$ be a finite set of clients and $F$ a set of facilities in a metric instance, with integer capacities $u_i > 0$ and facility costs $f_i \ge 0$. Let $X$ be a locally optimum solution of the capacitated facility location problem for the neighbourhood (9) (adding one copy of a facility, or dropping a set of copies and adding several copies of one facility). Then for every CFL solution $O$,
--
--   $$\mathrm{cost}_s(X) \le \mathrm{cost}_f(O) + \mathrm{cost}_s(O).$$
--
--   This is the paper's Lemma 5.1, a restatement of Lemma 4.1 for the uncapacitated problem: the service cost of a local optimum is bounded using only its optimality with respect to additions. Together with Lemma 5.3 it gives the locality gap 4 of Theorem 5.5.
--
--   **Formalization Note** $X$ is locally optimum with respect to the whole neighbourhood (9); only the add moves are needed. $O$ is any CFL solution with any capacity-feasible assignment, not necessarily an optimum.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 559, Lemma 5.1 (restating Lemma 4.1, p. 554)

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.1 (service cost)**, p. 559 (restating Lemma 4.1, p. 554): the service cost of a
locally optimum CFL solution `X` is at most the facility cost plus the service cost of any
CFL solution `O`: `cost_s(X) ≤ cost_f(O) + cost_s(O)`. -/
theorem service_cost_lemma_5_1 {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costS I X ≤ costF f O + costS I O := by sorry

end LocalSearchFL.CFL
