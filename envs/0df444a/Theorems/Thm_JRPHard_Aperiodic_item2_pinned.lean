-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_item2_pinned
-- name    : JRPHard.Aperiodic.item2_pinned
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:12.581953+00:00
-- url     : https://prove2.me/theorems/262c5ca0-d530-4d1a-9586-9e181acd8862
-- title:
--   Proof of Lemma 1, p. 9 — for q₂ ≠ M, JRP(q₁, q₂) ≥ EOQ_{K₂,H₂}(M) + K₀ + 4 > JRP(1, M)
-- statement:
--   Let $M$ be an odd composite number and let $\mathrm{JRP}$ be the aperiodic objective of the instance of Lemma 1 ($K_1 = K_0 = M(M-1)$, $H_1 = 4$, $K_2 = M^3(M^2-1)$, $H_2 = M(M^2-1)$). For all positive integers $q_1, q_2$ with $q_2 \ne M$,
--   $$\mathrm{JRP}(q_1,q_2) \ \ge\ 4q_1 + \min\{\mathrm{EOQ}_{K_2,H_2}(M-1),\ \mathrm{EOQ}_{K_2,H_2}(M+1)\}$$
--   and
--   $$\mathrm{JRP}(q_1,q_2) \ \ge\ \mathrm{EOQ}_{K_2,H_2}(M) + K_0 + 4 .$$
--   Moreover this lower bound already exceeds the value of the plan $(1, M)$:
--   $$\mathrm{JRP}(1, M) \ <\ \mathrm{EOQ}_{K_2,H_2}(M) + K_0 + 4 .$$
--
--   Together these show that every plan with $q_2 \ne M$ is strictly worse than $(1,M)$, so every optimal plan has $q_2 = M$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 9, proof of Lemma 1, "Optimal replenishment cycle for item 2"

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem item2_pinned (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (∀ q₁ q₂ : ℕ, 0 < q₁ → 0 < q₂ → q₂ ≠ M →
      4 * (q₁ : ℝ) + min (eoq2 M (M - 1)) (eoq2 M (M + 1)) ≤ lemma1Cost M q₁ q₂ ∧
      eoq2 M M + (coefK0 M : ℝ) + 4 ≤ lemma1Cost M q₁ q₂) ∧
    lemma1Cost M 1 M < eoq2 M M + (coefK0 M : ℝ) + 4 := by sorry

end JRPHard.Aperiodic
