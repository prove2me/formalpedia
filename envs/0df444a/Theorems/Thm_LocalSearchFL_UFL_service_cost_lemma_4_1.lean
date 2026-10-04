-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_service_cost_lemma_4_1
-- name    : LocalSearchFL.UFL.service_cost_lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:15:25.003026+00:00
-- url     : https://prove2.me/theorems/d9dcbf54-bffa-40ab-aa0b-6270c2a27900
-- title:
--   Lemma 4.1 (service cost): $\mathrm{cost}_s(S) \le \mathrm{cost}_f(O) + \mathrm{cost}_s(O)$
-- statement:
--   Let $C$ and $F$ be the clients and facilities of a metric instance with service costs $c_{ji}$, and let $f_i \ge 0$ be the opening cost of facility $i$. Let $S \subseteq F$ be a nonempty set of facilities that is locally optimum for the add/drop/swap neighbourhood
--   $$\mathcal B(S) = \{S + \{s'\}\} \cup \{S - \{s\} \mid s \in S\} \cup \{S - \{s\} + \{s'\} \mid s \in S\}.$$
--   Then for every nonempty set $O \subseteq F$ of facilities,
--   $$\mathrm{cost}_s(S) \le \mathrm{cost}_f(O) + \mathrm{cost}_s(O).$$
--
--   This bound on the service cost of a local optimum, due to Korupolu, Plaxton and Rajaraman, is one of the two halves of the locality gap bound of Theorem 4.3. It holds for every solution $O$, not only an optimal one, which is what makes the scaling argument of Theorem 4.4 possible.
--
--   **Formalization Note** $O$ ranges over all nonempty facility sets (the empty set has no service cost). The hypothesis is local optimality for the whole neighbourhood, as in the paper.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 554, Lemma 4.1

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Lemma 4.1 (service cost), p. 554. If `S` is a locally optimum solution for the add/drop/swap
neighbourhood (4), then for every solution `O`: `cost_s(S) ≤ cost_f(O) + cost_s(O)`. -/
theorem service_cost_lemma_4_1 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) :
    costS I S hS ≤ costF f O + costS I O hO := by sorry

end LocalSearchFL.UFL
