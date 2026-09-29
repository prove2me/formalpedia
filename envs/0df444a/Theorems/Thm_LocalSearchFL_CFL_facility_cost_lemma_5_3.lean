-- Prove2me | Theorems.Thm_LocalSearchFL_CFL_facility_cost_lemma_5_3
-- name    : LocalSearchFL.CFL.facility_cost_lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:24:43.333125+00:00
-- url     : https://prove2.me/theorems/7ffbedf6-f444-48f5-abb2-6ad04bb1666a
-- title:
--   Lemma 5.3 — facility cost of a CFL local optimum is at most 3 cost_f(O) + 2 cost_s(O)
-- statement:
--   Let $C$ be a nonempty finite set of clients and $F$ a set of facilities in a metric instance, with integer capacities $u_i > 0$ and facility costs $f_i \ge 0$. Let $X$ be a locally optimum CFL solution for the neighbourhood (9). Then for every CFL solution $O$,
--
--   $$\mathrm{cost}_f(X) \le 3\,\mathrm{cost}_f(O) + 2\,\mathrm{cost}_s(O).$$
--
--   Added to Lemma 5.1, this gives $\mathrm{cost}(X) \le 4\,\mathrm{cost}_f(O) + 3\,\mathrm{cost}_s(O) \le 4\,\mathrm{cost}(O)$, the locality gap of Theorem 5.5.
--
--   **Formalization Note** The hypothesis that there is at least one client is added: without clients, a single idle copy of a facility with $f = 1$, $u = 1$ is locally optimum, and the empty solution $O$ violates the inequality.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 559, Lemma 5.3 (proof completed p. 560)

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.3 (facility cost)**, p. 559: the facility cost of a locally optimum CFL solution
`X` (at least one client) satisfies `cost_f(X) ≤ 3 · cost_f(O) + 2 · cost_s(O)` for every CFL
solution `O`. -/
theorem facility_cost_lemma_5_3 {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costF f X ≤ 3 * costF f O + 2 * costS I O := by sorry

end LocalSearchFL.CFL
