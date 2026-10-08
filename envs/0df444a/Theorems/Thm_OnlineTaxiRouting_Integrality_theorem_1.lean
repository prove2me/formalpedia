-- Prove2me | Theorems.Thm_OnlineTaxiRouting_Integrality_theorem_1
-- name    : OnlineTaxiRouting.Integrality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:19.093983+00:00
-- url     : https://prove2.me/theorems/b869263a-afb7-4d2d-b52e-e0c797b3b86b
-- title:
--   Theorem 1, p. 13 — with fixed pick-up times the MIO formulation (5)–(14) is integral
-- statement:
--   Let $\mathcal C$ be a finite set of customers and $\mathcal K$ a finite set of taxis, with data $t^{\min}, t^{\max}, t^{\mathrm{init}}, T, R$ as in the taxi routing model, and assume (standing assumption of §2.1) that the graph $\mathcal G$ defined by the arc rule $t^{\min}_c + T_{c,c'} \le t^{\max}_{c'}$ is acyclic. Suppose that every customer has a fixed pick-up time,
--   $$t^{\min}_c = t^{\max}_c = t^*_c \qquad \forall c \in \mathcal C.$$
--   Then the mixed-integer formulation (5)–(14) is integral: every extreme point $(x, y, p, t)$ of its LP relaxation — constraints (6)–(8), (12)–(14) and $0 \le x, y, p \le 1$ — has
--   $$x_{c',c},\ y_{k,c},\ p_c \in \{0, 1\} \quad \text{for all } c', c \in \mathcal C,\ k \in \mathcal K.$$
--
--   Integrality is a property of the feasible region, so the objective (5) plays no role in the statement. As a consequence, when pick-up times are fixed, the offline taxi routing problem can be solved by linear programming (for instance by the simplex method), and this underlies the paper's `maxflow` heuristic for problems with time windows.
--
--   **Formalization Note** Integrality concerns only the binary variables $x, y, p$; the times $t$ are continuous and are equal to $t^*$ at every feasible point. The acyclicity hypothesis is the standing assumption of the paper's §2.1 and is kept, although the conclusion does not depend on it.
-- source:
--   Bertsimas–Jaillet–Martin, accepted manuscript (March 2018), Theorem 1, p. 13

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting

namespace OnlineTaxiRouting.Integrality

theorem theorem_1 {C K : Type*} [Fintype C] [Fintype K] (I : Instance C K)
    (hacyc : I.Acyclic) (hfix : ∀ c, I.tmin c = I.tmax c) :
    IsIntegral (relax I) := by sorry

end OnlineTaxiRouting.Integrality
