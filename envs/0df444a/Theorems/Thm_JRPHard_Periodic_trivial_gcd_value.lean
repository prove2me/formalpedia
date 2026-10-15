-- Prove2me | Theorems.Thm_JRPHard_Periodic_trivial_gcd_value
-- name    : JRPHard.Periodic.trivial_gcd_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:34.205282+00:00
-- url     : https://prove2.me/theorems/9a660da6-ae08-488e-840d-73a28342d9d9
-- title:
--   Proof of Lemma 2, p. 12 — if gcd(q, M) = 1 or gcd(q, M) = M, then M/gcd(q, M) + q ≥ M
-- statement:
--   Let $M$ be a natural number and $q$ a positive integer with $\gcd(q,M) = 1$ or $\gcd(q,M) = M$. Then the objective of problem (4) at $q$ satisfies
--   $$\frac{M}{\gcd(q,M)} + q \ge M.$$
--
--   A period $q_1$ that shares no non-trivial factor with $M$ (or is a multiple of $M$) therefore costs at least $M$ in problem (4), more than the value $2M/3$ attained at a non-trivial divisor; so every optimal $q_1$ has $1 < \gcd(q_1,M) < M$.
--
--   **Formalization Note** The paper states this for the odd composite $M$ of Lemma 2; it holds for every natural number $M$, which is how it is stated.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 12, §2.2, proof of Lemma 2, first sentence of p. 12

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem trivial_gcd_value (M q : ℕ) (hq : 0 < q)
    (hg : Nat.gcd q M = 1 ∨ Nat.gcd q M = M) :
    (M : ℝ) ≤ obj4 M q := by sorry

end JRPHard.Periodic
