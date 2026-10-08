-- Prove2me | Theorems.Thm_OnlineTaxiRouting_Integrality_flowRelax_extreme_zeroOne
-- name    : OnlineTaxiRouting.Integrality.flowRelax_extreme_zeroOne
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:07.912754+00:00
-- url     : https://prove2.me/theorems/5e60a581-5c5d-4ec8-952d-8932dcf70d27
-- title:
--   §3.2, pp. 12–13 — the relaxed network-flow system (6)–(11) on any arc subset has 0/1 extreme points
-- statement:
--   Let $\mathcal C$ and $\mathcal K$ be finite sets of customers and taxis, and let $A \subseteq \mathcal C \times \mathcal C$ and $B \subseteq \mathcal K \times \mathcal C$ be arbitrary sets of arcs. Let $P_{A,B}$ be the set of $(x, y, p)$ with
--   $$p_c = \sum_{k} y_{k,c} + \sum_{c'} x_{c',c}\ \forall c, \quad \sum_{c} x_{c',c} \le p_{c'}\ \forall c', \quad \sum_c y_{k,c} \le 1\ \forall k, \quad 0 \le x, y, p \le 1,$$
--   and $x_{c',c} = 0$ for $(c',c) \notin A$, $y_{k,c} = 0$ for $(k,c) \notin B$. Then every extreme point of $P_{A,B}$ has all coordinates $x_{c',c}$, $y_{k,c}$, $p_c$ in $\{0,1\}$.
--
--   The paper observes that the constraints (6)–(11) describe a max-flow problem with integer bounds, so that the extreme points of the relaxation are integral and the simplex method returns an integral optimum; the proof of Theorem 1 ends by applying the same fact to the system in which some variables have been removed.
--
--   **Formalization Note** The page states the claim for the variables on the arcs of $\mathcal G$ (and, in the proof of Theorem 1, for the system with variables removed). The statement here quantifies over every arc subset, which covers both cases ($A$, $B$ everything is the system (6)–(11) as printed). No acyclicity is assumed: $A$ may contain cycles and loops $(c, c)$.
-- source:
--   Bertsimas–Jaillet–Martin, accepted manuscript (March 2018), §3.2, Max Flow Heuristic, pp. 12–13; proof of Theorem 1, p. 13

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting

namespace OnlineTaxiRouting.Integrality

theorem flowRelax_extreme_zeroOne {C K : Type*} [Fintype C] [Fintype K]
    (A : C → C → Prop) (B : K → C → Prop) :
    ∀ w ∈ Set.extremePoints ℝ (flowRelax A B), IsZeroOneFlow w := by sorry

end OnlineTaxiRouting.Integrality
