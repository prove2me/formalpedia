-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_multiple_upper_bound
-- name    : JRPHard.Aperiodic.multiple_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:25.349849+00:00
-- url     : https://prove2.me/theorems/8dcd8bce-311a-4fb4-a3f4-9d027fb0450f
-- title:
--   Proof of Lemma 1, p. 9 — for a multiple q of a divisor p of M, DC(q, M; K₀) ≥ p(M − 1)/q and JRP^red(q) ≤ (M − 1)(M − p)/q + 4q
-- statement:
--   Let $M$ be an odd composite number, let $p$ be a divisor of $M$ with $3 \le p < M$, and let $q$ be a positive multiple of $p$. Then the discount satisfies
--   $$\mathrm{DC}(q, M; K_0) = \frac{M(M-1)}{\mathrm{lcm}(q,M)} \ \ge\ \frac{p(M-1)}{q},$$
--   and therefore
--   $$\mathrm{JRP}^{\mathrm{red}}(q) \ \le\ \frac{(M-1)(M-p)}{q} + 4q .$$
--
--   This upper bound on periods that share the factor $p$ with $M$ is the comparison function used to exhibit a period with $\mathrm{JRP}^{\mathrm{red}} < 4(M-1)$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 9, proof of Lemma 1, "Let p be a non-trivial divisor of M such that 3 ≤ p < M"

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem multiple_upper_bound (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hplt : p < M) (q : ℕ) (hq : 0 < q) (hpq : p ∣ q) :
    (p : ℝ) * ((M : ℝ) - 1) / (q : ℝ) ≤ (coefK0 M : ℝ) / (Nat.lcm q M : ℝ) ∧
      jrpRed M q ≤ ((M : ℝ) - 1) * ((M : ℝ) - p) / (q : ℝ) + 4 * (q : ℝ) := by sorry

end JRPHard.Aperiodic
