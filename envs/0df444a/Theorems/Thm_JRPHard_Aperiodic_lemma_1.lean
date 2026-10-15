-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_lemma_1
-- name    : JRPHard.Aperiodic.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:17.816918+00:00
-- url     : https://prove2.me/theorems/14f78d2d-486a-4438-92ef-e148c8fd910f
-- title:
--   Lemma 1 — for odd composite M, every optimal plan of the explicit aperiodic instance has q₂ = M and 1 < gcd(q₁, M) < M
-- statement:
--   Let $M$ be an odd composite number. Consider the two-item aperiodic joint replenishment problem
--   $$\min\left\{\mathrm{JRP}(q_1,q_2) = \frac{K_1}{q_1} + H_1 q_1 + \frac{K_2}{q_2} + H_2 q_2 - \frac{K_0}{\mathrm{lcm}(q_1,q_2)} \ :\ q_1, q_2 \in \mathbb Z^+\right\}$$
--   with the coefficients
--   $$K_1 = K_0 = M(M-1), \qquad H_1 = 4, \qquad K_2 = M^3(M^2-1), \qquad H_2 = M(M^2-1).$$
--   Then:
--
--   1. the instance is a valid aperiodic JRP instance, $K_0 \le K_1$ and $K_0 \le K_2$, and every coefficient is at most $M^5$ (so its binary size is at most $5\log M$);
--   2. the problem has an optimal solution;
--   3. every optimal solution $(q_1, q_2)$ satisfies
--   $$q_2 = M \qquad\text{and}\qquad 1 < \gcd(q_1, M) < M .$$
--
--   Thus an exact algorithm for the two-item aperiodic JRP yields a non-trivial divisor $\gcd(q_1,M)$ of $M$; this is the mathematical core of the paper's Theorem 1(a), the reduction from integer factorization.
--
--   **Formalization Note** The paper states the lemma as "there is a two-item instance … whose optimal solutions satisfy …"; here the instance is the explicit one constructed in the proof (p. 9), which is what the reduction uses and which rules out choosing an instance that does not depend on $M$ in the intended way. The existence of an optimal solution is stated explicitly, so that the claim about every optimal solution is not vacuous; it holds because the objective tends to infinity. "Size at most $5\log M$" is rendered as "every coefficient is at most $M^5$", equivalent in any logarithm base. Odd composite is encoded as `Odd M`, `1 < M`, `¬ M.Prime`. Periods range over positive integers only. The polynomial running time of the reduction is not formalized.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 8, Lemma 1 (instance from the proof, p. 9)

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem lemma_1 (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (coefK0 M ≤ coefK1 M ∧ coefK0 M ≤ coefK2 M ∧
      coefK0 M ≤ M ^ 5 ∧ coefK1 M ≤ M ^ 5 ∧ coefK2 M ≤ M ^ 5 ∧ coefH1 ≤ M ^ 5 ∧
      coefH2 M ≤ M ^ 5) ∧
    (∃ q₁ q₂ : ℕ, IsOptimal (lemma1Cost M) q₁ q₂) ∧
    ∀ q₁ q₂ : ℕ, IsOptimal (lemma1Cost M) q₁ q₂ →
      q₂ = M ∧ 1 < Nat.gcd q₁ M ∧ Nat.gcd q₁ M < M := by sorry

end JRPHard.Aperiodic
