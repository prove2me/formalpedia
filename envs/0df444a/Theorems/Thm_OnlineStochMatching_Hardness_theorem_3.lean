-- Prove2me | Theorems.Thm_OnlineStochMatching_Hardness_theorem_3
-- name    : OnlineStochMatching.Hardness.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:01:25.9108+00:00
-- url     : https://prove2.me/theorems/a0483e8a-0423-4120-847c-fee58083b8fc
-- title:
--   Theorem 3 — no online algorithm beats 26/27 on a 6-cycle, and none reaches 1 − o(1) on k disjoint 6-cycles
-- statement:
--   This is Theorem 3 of Feldman, Mehta, Mirrokni and Muthukrishnan, in two parts.
--
--   1. **A single instance.** On the 6-cycle instance (advertisers $\{a,b,c\}$, impression types $\{x,y,z\}$, edges $\{(x,a),(y,a),(y,b),(z,b),(z,c),(x,c)\}$, uniform distribution, $n = 3$), every randomized online algorithm has
--   $$\mathbb E\!\left[\frac{\mathrm{ALG}}{\mathrm{OPT}}\right] \le \frac{26}{27}.$$
--   2. **A family with $n \to \infty$.** For $k \ge 1$ let $\Gamma_k$ be the instance made of $k$ disjoint copies of the 6-cycle, with the uniform distribution on its $3k$ impression types and $n = 3k$ arrivals. There are a constant $c < 1$ and a threshold $K_0$ such that for every $k \ge K_0$ and every randomized online algorithm on $\Gamma_k$,
--   $$\mathbb E\!\left[\frac{\mathrm{ALG}}{\mathrm{OPT}}\right] \le c.$$
--
--   The paper writes the second part as "there exists a family of instances with $n \to \infty$ for which no algorithm can achieve an expected approximation of $1 - o(1)$"; part 2 is the explicit form of that statement on the paper's own family: the best achievable expected approximation factor on $\Gamma_k$ stays below a fixed constant smaller than $1$ for all large $k$, so it does not tend to $1$.
--
--   The theorem shows that the expected approximation factor of online algorithms in the i.i.d. model is bounded strictly away from $1$, which separates the problem from its offline version and frames the paper's positive results ($1 - 1/e$ and $0.67$).
--
--   **Formalization Note** Expectations are over the algorithm's randomness (a probability distribution on deterministic online algorithms) and the uniform i.i.d. arrivals. The constant $c$ and the threshold $K_0$ are chosen before $k$ and before the algorithm. The paper's numerical value $c \approx 0.9898$ (Appendix B) rests on approximations and is not part of the statement. On these instances every impression type has an adjacent advertiser, so $\mathrm{OPT} \ge 1$ on every arrival sequence and the ratio is never $0/0$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Theorem 3; p. 13, Appendix B

import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle

namespace OnlineStochMatching.Hardness

/-- Theorem 3 (p. 4; details App. B, p. 13). (a) On the 6-cycle instance (`n = 3`), no randomized
online algorithm has expected approximation factor above `26/27`. (b) On the family of `k`
disjoint 6-cycles with uniform arrivals and `n = 3k`, there is a constant `c < 1` such that for
all large `k` no randomized online algorithm has expected approximation factor above `c`; so
the best achievable expected factor does not tend to `1` as `n → ∞`. -/
theorem theorem_3 :
    (∀ P : PMF (OnlineAlg Adv Imp 3), randExpectedRatio cycleEdge P ≤ 26 / 27) ∧
    ∃ c : ℝ, c < 1 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∀ P : PMF (OnlineAlg (Fin k × Adv) (Fin k × Imp) (3 * k)),
        randExpectedRatio (kCycleEdge k) P ≤ c := by sorry

end OnlineStochMatching.Hardness
