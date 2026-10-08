-- Prove2me | Theorems.Thm_OnlineStochMatching_Hardness_xyy_scenario
-- name    : OnlineStochMatching.Hardness.xyy_scenario
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:00:46.476445+00:00
-- url     : https://prove2.me/theorems/0f69bc86-b24c-4995-a40e-3308ea9d0ebb
-- title:
--   §3, p. 4 — on the 6-cycle every online algorithm loses an impression on some scenario (u, v, v) where OPT = 3
-- statement:
--   Consider the 6-cycle instance: advertisers $\{a, b, c\}$, impression types $\{x, y, z\}$, edges $\{(x,a),(y,a),(y,b),(z,b),(z,c),(x,c)\}$, and $n = 3$ arrivals. Let $\mathcal A$ be any deterministic online algorithm and let $u \in \{x, y, z\}$ be the type of the first arrival. Then there is a type $v$ such that, on the arrival sequence $(u, v, v)$,
--
--   $$\mathrm{ALG}(u, v, v) \le 2 \qquad\text{and}\qquad \mathrm{OPT}(u, v, v) = 3.$$
--
--   In the paper's case the first arrival is $x$ and the algorithm assigns it to $a$; then $v = y$: both $y$ impressions are adjacent only to $a$ and $b$, so at most one of them can be assigned, while with hindsight $x \to c$, $y \to a$, $y \to b$ assigns all three. The statement covers every first type and every first decision (assigning to either neighbour, or not assigning at all).
--
--   Since the algorithm's first decision depends only on $u$, and each scenario $(u, v, v)$ has probability $1/27$, this places a ratio $\mathrm{ALG}/\mathrm{OPT} \le 2/3$ on a set of scenarios of total probability $1/9$, which is what drives the bound $26/27$ of Theorem 3.
--
--   **Formalization Note** The paper's "without loss of generality (from the symmetry of the 6-cycle)" is replaced by quantifying over every first type $u$; the algorithm's first decision is whatever it does on $u$. The arrival sequence is written `![u, v, v]`.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Section 3, the (x, y, y) argument preceding Theorem 3

import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle

namespace OnlineStochMatching.Hardness

/-- §3, p. 4 (the "(x, y, y)" argument behind Theorem 3). On the 6-cycle with `n = 3` arrivals,
for every deterministic online algorithm and every type `u` of the first arrival there is a type
`v` such that on the scenario `(u, v, v)` the algorithm assigns at most two arrivals while the
optimum assigns all three. (The paper's case: `u = x` assigned to `a`, `v = y`.) -/
theorem xyy_scenario (alg : OnlineAlg Adv Imp 3) (u : Imp) :
    ∃ v : Imp, ALG cycleEdge alg ![u, v, v] ≤ 2 ∧ OPT cycleEdge ![u, v, v] = 3 := by sorry

end OnlineStochMatching.Hardness
