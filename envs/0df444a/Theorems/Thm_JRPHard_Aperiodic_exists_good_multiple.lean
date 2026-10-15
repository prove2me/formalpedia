-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_exists_good_multiple
-- name    : JRPHard.Aperiodic.exists_good_multiple
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:18.93426+00:00
-- url     : https://prove2.me/theorems/c4ebdc26-3408-47c2-aba0-382c32bc836c
-- title:
--   Proof of Lemma 1, pp. 9–10 — the interval [(M − 1)/2 − (p − 1)/2, (M − 1)/2 + (p − 1)/2] contains a multiple q of p with JRP^red(q) < 4(M − 1)
-- statement:
--   Let $M$ be an odd composite number and let $p$ be a divisor of $M$ with $3 \le p < M$ (so $p$ is odd). Then there is a positive integer $q$ that is a multiple of $p$, lies in the integer interval
--   $$\left[\frac{M-1}{2} - \frac{p-1}{2},\ \frac{M-1}{2} + \frac{p-1}{2}\right] \cap \mathbb Z^+,$$
--   and satisfies
--   $$\mathrm{JRP}^{\mathrm{red}}(q) \ <\ 4(M-1).$$
--
--   Combined with the coprime lower bound, this shows that every minimizer $q_1^*$ of problem (2) satisfies $\gcd(q_1^*, M) > 1$.
--
--   **Formalization Note** Because $M$ and $p$ are odd, both endpoints are integers; they are written with natural-number division and subtraction, `(M - 1) / 2 - (p - 1) / 2` and `(M - 1) / 2 + (p - 1) / 2`, which are exact here (and the lower endpoint $(M-p)/2$ is positive since $p < M$).
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, pp. 9–10, proof of Lemma 1, "This upper bound, as a continuous function of q, is strictly convex …"

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem exists_good_multiple (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hplt : p < M) :
    ∃ q : ℕ, 0 < q ∧ p ∣ q ∧
      (M - 1) / 2 - (p - 1) / 2 ≤ q ∧ q ≤ (M - 1) / 2 + (p - 1) / 2 ∧
      jrpRed M q < 4 * ((M : ℝ) - 1) := by sorry

end JRPHard.Aperiodic
