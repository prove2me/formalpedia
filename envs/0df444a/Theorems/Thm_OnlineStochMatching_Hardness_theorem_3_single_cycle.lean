-- Prove2me | Theorems.Thm_OnlineStochMatching_Hardness_theorem_3_single_cycle
-- name    : OnlineStochMatching.Hardness.theorem_3_single_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:01:11.006069+00:00
-- url     : https://prove2.me/theorems/774c4841-c044-462d-ad84-c7ddb590c145
-- title:
--   Theorem 3 (first sentence) — no online algorithm beats expected approximation factor 26/27 on the 6-cycle
-- statement:
--   Consider the 6-cycle instance: advertisers $\{a, b, c\}$, impression types $\{x, y, z\}$, edges $\{(x,a),(y,a),(y,b),(z,b),(z,c),(x,c)\}$, the uniform distribution on the three types, and $n = 3$ arrivals. For every randomized online algorithm, the expected approximation factor satisfies
--
--   $$\mathbb E\!\left[\frac{\mathrm{ALG}}{\mathrm{OPT}}\right] \le \frac{26}{27},$$
--
--   where the expectation is over the algorithm's randomness and the three i.i.d. uniform arrivals.
--
--   This is the first sentence of Theorem 3: there is an instance of the online stochastic matching problem on which no algorithm can achieve an expected approximation factor better than $26/27$. It shows that, unlike the offline problem, the online i.i.d. problem has no algorithm with expected factor arbitrarily close to $1$ on every instance.
--
--   **Formalization Note** A randomized online algorithm is a probability distribution `P` on deterministic online algorithms (see the model definition); the bound holds for every such `P`. On this instance every arrival has an adjacent advertiser, so $\mathrm{OPT} \ge 1$ on every arrival sequence and the ratio is never $0/0$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Theorem 3 (first sentence) and the 6-cycle instance of Section 3

import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle

namespace OnlineStochMatching.Hardness

/-- Theorem 3, first sentence (p. 4): on the 6-cycle instance (three advertisers, three
impression types, uniform arrivals, `n = 3`), every randomized online algorithm has expected
approximation factor `E[ALG/OPT]` at most `26/27`. -/
theorem theorem_3_single_cycle (P : PMF (OnlineAlg Adv Imp 3)) :
    randExpectedRatio cycleEdge P ≤ 26 / 27 := by sorry

end OnlineStochMatching.Hardness
