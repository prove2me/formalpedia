-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_lemma_3
-- name    : JRPHard.RangeDiv.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:08.848173+00:00
-- url     : https://prove2.me/theorems/bfd6763e-b5f9-4e4e-bdd9-1871946aa9c7
-- title:
--   Lemma 3 — M has a divisor in [L, U] iff the explicit periodic instance JRP_{M,U,L} has a plan of cost at most L + U + 2M²(M + 1)
-- statement:
--   Let $M \ge U \ge L > 0$ be integers with $L + U < 2\sqrt{2LU}$ (an instance of RangeDivisor). Consider the two-item periodic JRP instance $\mathrm{JRP}_{M,U,L}$,
--   $$\mathrm{JRP}_{M,U,L}(q_1,q_2) = q_1 + \frac{M^3(M+1)}{q_2} + M(M+1)\,q_2 + \frac{LU}{\gcd(q_1,q_2)},$$
--   that is, objective (3) with $K_0 = LU$, $K_1 = 0$, $H_1 = 1$, $K_2 = M^3(M+1)$, $H_2 = M(M+1)$. Then:
--
--   1. every coefficient $K_0, K_2, H_2$ is a natural number at most $2M^4$ (and $K_1 = 0$, $H_1 = 1$), so each has bit length polynomial in $\log M$;
--   2. $M$ has a divisor $q$ with $L \le q \le U$ if and only if there are positive integers $q_1, q_2$ with
--   $$\mathrm{JRP}_{M,U,L}(q_1, q_2) \ \le\ L + U + 2M^2(M+1).$$
--
--   This is the mathematical content of the reduction from RangeDivisor to the two-item periodic JRP, which, combined with Shor's NP-completeness of RangeDivisor under randomized reductions, gives Theorem 2 of the paper.
--
--   **Formalization Note** The printed lemma compares "the optimal value of $\mathrm{JRP}_{M,U,L}$" with $L + U$. The two-item objective also contains item 2's cost $\mathrm{EOQ}_{K_2,H_2}(M) = 2M^2(M+1)$ at $q_2 = M$, so the printed comparison is never met. The statement uses the threshold $z_{M,L,U} = L + U + 2M^2(M+1)$ that §3.1 announces. "Optimal value $\le z$" is stated in the decision form of p. 13, "is there a solution of cost at most $z$"; the two agree because the minimum is attained. $K_2, H_2$ are Lemma 2's values, where the page says "sufficiently large". "Polynomial time" is not formalized; the explicit coefficients and the bound $2M^4$ are what remain of it. The bound is $2M^4$ rather than $M^4$ because $M = L = U = 1$ is an instance, with $K_2 = 2$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, pp. 13–14, Lemma 3 (threshold z_{M,L,U} of §3.1, p. 13; decision version, p. 13)

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem lemma_3 (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) :
    (coefK0 L U ≤ 2 * M ^ 4 ∧ JRPHard.Periodic.coefK2 M ≤ 2 * M ^ 4 ∧ JRPHard.Periodic.coefH2 M ≤ 2 * M ^ 4) ∧
    (HasDivisorIn M L U ↔
      ∃ q₁ q₂ : ℕ, 0 < q₁ ∧ 0 < q₂ ∧ rangeCost M L U q₁ q₂ ≤ threshold M L U) := by sorry

end JRPHard.RangeDiv
