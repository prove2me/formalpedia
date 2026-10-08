-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_facility_cost_lemma_4_2
-- name    : LocalSearchFL.UFL.facility_cost_lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:18:22.254369+00:00
-- url     : https://prove2.me/theorems/30b46755-ca27-41dd-9149-8b8a1307399e
-- title:
--   Lemma 4.2 (facility cost): $\mathrm{cost}_f(S) \le \mathrm{cost}_f(O) + 2\,\mathrm{cost}_s(O)$
-- statement:
--   Let $C$ and $F$ be the clients and facilities of a metric instance, and let $f_i \ge 0$ be the opening cost of facility $i$. Let $S \subseteq F$ be a nonempty set of facilities that is locally optimum for the add/drop/swap neighbourhood (4). Then for every nonempty set $O \subseteq F$,
--   $$\mathrm{cost}_f(S) \le \mathrm{cost}_f(O) + 2 \cdot \mathrm{cost}_s(O).$$
--
--   Together with Lemma 4.1 this gives the locality gap 3 of Theorem 4.3; the asymmetry between the coefficients of the two lemmas is what the scaling argument of Theorem 4.4 exploits.
--
--   **Formalization Note** No assumption that clients exist is made: with no clients the statement reduces to $\mathrm{cost}_f(S) \le \mathrm{cost}_f(O)$, which the drop and swap moves still give.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 555, Lemma 4.2 (proof pp. 555–556)

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- Lemma 4.2 (facility cost), p. 555. If `S` is a locally optimum solution for the
add/drop/swap neighbourhood (4), then for every solution `O`:
`cost_f(S) ≤ cost_f(O) + 2 · cost_s(O)`. -/
theorem facility_cost_lemma_4_2 {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) :
    costF f S ≤ costF f O + 2 * costS I O hO := by sorry

end LocalSearchFL.UFL
