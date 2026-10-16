-- Prove2me | Theorems.Thm_JRPHard_Periodic_item2_pinned
-- name    : JRPHard.Periodic.item2_pinned
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:44.314054+00:00
-- url     : https://prove2.me/theorems/d7c1fc23-9e18-4c25-86d2-3db31702e918
-- title:
--   Proof of Lemma 2, p. 11 — for q₂ ≠ M, JRP(q₁, q₂) > M + EOQ_{K₂,H₂}(M) + 1 = JRP(M, M)
-- statement:
--   Let $M \ge 2$ and let $\mathrm{JRP}_M$ be the periodic JRP objective of the Lemma 2 instance ($K_0 = M$, $K_1 = 0$, $H_1 = 1$, $H_2 = M(M+1)$, $K_2 = M^3(M+1)$), with $\mathrm{EOQ}_2$ item 2's EOQ cost. Then for all positive integers $q_1, q_2$ with $q_2 \neq M$,
--   $$\mathrm{JRP}_M(q_1,q_2) > M + \mathrm{EOQ}_2(M) + 1,$$
--   and
--   $$\mathrm{JRP}_M(M,M) = M + \mathrm{EOQ}_2(M) + 1.$$
--
--   Hence every $q_2 \neq M$ is strictly sub-optimal: item 2's period is pinned at $M$ in every optimal solution.
--
--   **Formalization Note** Stated for every $M \ge 2$; the paper's context is an odd composite $M$. Periods range over positive integers.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 11, §2.2, proof of Lemma 2, "Optimal replenishment cycle for item 2", sentence after the display

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem item2_pinned (M : ℕ) (hM : 2 ≤ M) :
    (∀ q₁ q₂ : ℕ, 0 < q₁ → 0 < q₂ → q₂ ≠ M →
      (M : ℝ) + eoq2 M M + 1 < lemma2Cost M q₁ q₂) ∧
    lemma2Cost M M M = (M : ℝ) + eoq2 M M + 1 := by sorry

end JRPHard.Periodic
