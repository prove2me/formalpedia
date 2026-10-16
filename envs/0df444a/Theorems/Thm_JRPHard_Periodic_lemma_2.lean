-- Prove2me | Theorems.Thm_JRPHard_Periodic_lemma_2
-- name    : JRPHard.Periodic.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:45.826579+00:00
-- url     : https://prove2.me/theorems/98ea3b3b-6ea5-4af6-974e-93acce2ce3f0
-- title:
--   Lemma 2 — for odd composite M, every optimal plan of the explicit periodic instance has q₂ = M and 1 < gcd(q₁, M) < M
-- statement:
--   Let $M$ be an odd composite number. Consider the two-item periodic joint replenishment instance
--   $$\min\Big\{ \mathrm{JRP}_M(q_1,q_2) = \frac{K_1}{q_1} + H_1 q_1 + \frac{K_2}{q_2} + H_2 q_2 + \frac{K_0}{\gcd(q_1,q_2)} \;:\; q_1, q_2 \in \mathbb{Z}^+ \Big\}$$
--   with
--   $$K_0 = M,\quad K_1 = 0,\quad H_1 = 1,\quad H_2 = M(M+1),\quad K_2 = M^3(M+1).$$
--   Then:
--   1. $K_0 > 0$, and every coefficient $K_0, K_1, K_2, H_1, H_2$ is a natural number at most $M^5$ (so its size is at most $5\log M$);
--   2. the instance has an optimal solution;
--   3. every optimal solution $(q_1,q_2)$ satisfies
--   $$q_2 = M \quad\text{and}\quad 1 < \gcd(q_1, M) < M.$$
--
--   Thus $\gcd(q_1,M)$ is a non-trivial divisor of $M$ for any optimal solution, so an exact solver for the two-item periodic JRP factors odd composite numbers. This is the mathematical core of Theorem 1(b) of the paper.
--
--   **Formalization Note** The paper states "there is a two-item instance"; the instance here is the explicit one built in the first sentence of the proof (a stronger statement). The paper's "whose optimal solutions satisfy" is formalized as existence of an optimal solution together with the property for every optimal solution, so the claim is not vacuous. "Size at most $5\log(M)$" is stated as "at most $M^5$", which is the same bound in any logarithm base. $K_0 > 0$ is the model's assumption (p. 10). Optimal solutions may be non-unique (for $M = 15$ both $q_1 = 3$ and $q_1 = 5$ are optimal); nothing about which divisor appears is claimed. Odd composite is encoded as: odd, $M > 1$, and $M$ not prime. Polynomial running time (Theorem 1(b) itself) is not formalized.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 11, Lemma 2 (instance from the first sentence of its proof)

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem lemma_2 (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (0 < coefK0 M ∧
      coefK0 M ≤ M ^ 5 ∧ coefK1 ≤ M ^ 5 ∧ coefK2 M ≤ M ^ 5 ∧ coefH1 ≤ M ^ 5 ∧
      coefH2 M ≤ M ^ 5) ∧
    (∃ q₁ q₂ : ℕ, JRPHard.Aperiodic.IsOptimal (lemma2Cost M) q₁ q₂) ∧
    ∀ q₁ q₂ : ℕ, JRPHard.Aperiodic.IsOptimal (lemma2Cost M) q₁ q₂ →
      q₂ = M ∧ 1 < Nat.gcd q₁ M ∧ Nat.gcd q₁ M < M := by sorry

end JRPHard.Periodic
