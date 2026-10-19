-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_multiple_of_M
-- name    : JRPHard.Aperiodic.multiple_of_M
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:26.532165+00:00
-- url     : https://prove2.me/theorems/0320f0d1-4316-4a4c-bcd4-ae19754809a0
-- title:
--   Proof of Lemma 1, p. 10 — multiples q₁ of M have JRP^red(q₁) = 4q₁ ≥ 4M, while JRP^red((M − 1)/2) ≤ 4(M − 1)
-- statement:
--   Let $M$ be an odd composite number.
--
--   1. If $q$ is a positive multiple of $M$, then every replenishment of item 1 is a joint one, and
--   $$\mathrm{JRP}^{\mathrm{red}}(q) = 4q \ \ge\ 4M .$$
--   2. At the period $(M-1)/2$,
--   $$\mathrm{JRP}^{\mathrm{red}}\!\left(\frac{M-1}{2}\right) \ \le\ 4(M-1).$$
--
--   Since $4(M-1) < 4M$, no multiple of $M$ minimizes problem (2); hence every minimizer $q_1^*$ satisfies $\gcd(q_1^*, M) < M$.
--
--   **Formalization Note** $(M-1)/2$ is natural-number division, exact because $M$ is odd.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 10, proof of Lemma 1, "Next, let us show that gcd(q₁*, M) < M"

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem multiple_of_M (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (∀ q : ℕ, 0 < q → M ∣ q → jrpRed M q = 4 * (q : ℝ) ∧ 4 * (M : ℝ) ≤ jrpRed M q) ∧
      jrpRed M ((M - 1) / 2) ≤ 4 * ((M : ℝ) - 1) := by sorry

end JRPHard.Aperiodic
