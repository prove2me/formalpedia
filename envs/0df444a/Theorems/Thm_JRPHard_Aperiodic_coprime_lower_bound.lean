-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_coprime_lower_bound
-- name    : JRPHard.Aperiodic.coprime_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:22.491661+00:00
-- url     : https://prove2.me/theorems/570a0e05-9ed3-44ef-ab5d-4ef57278ca57
-- title:
--   Proof of Lemma 1, p. 9 — for q₁ coprime with M, JRP^red(q₁) = (M − 1)²/q₁ + 4q₁ ≥ 4(M − 1)
-- statement:
--   Let $M$ be an odd composite number and let $q$ be a positive integer coprime with $M$. Then $\mathrm{lcm}(q, M) = qM$, the reduced objective of problem (2) is
--   $$\mathrm{JRP}^{\mathrm{red}}(q) = \frac{(M-1)^2}{q} + 4q ,$$
--   and consequently
--   $$\mathrm{JRP}^{\mathrm{red}}(q) \ \ge\ \min_{x \in \mathbb R,\, x>0}\left\{\frac{(M-1)^2}{x} + 4x\right\} = 4(M-1).$$
--   Both the identity and the inequality are asserted.
--
--   So no period sharing no factor with $M$ can do better than $4(M-1)$; an optimal $q_1$ must share a non-trivial factor with $M$ as soon as some other period beats $4(M-1)$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 9, proof of Lemma 1, "First, let us show that gcd(q₁*, M) > 1"

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem coprime_lower_bound (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q M) :
    jrpRed M q = ((M : ℝ) - 1) ^ 2 / (q : ℝ) + 4 * (q : ℝ) ∧
      4 * ((M : ℝ) - 1) ≤ jrpRed M q := by sorry

end JRPHard.Aperiodic
