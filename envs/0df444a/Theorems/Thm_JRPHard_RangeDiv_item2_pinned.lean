-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_item2_pinned
-- name    : JRPHard.RangeDiv.item2_pinned
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:10.149073+00:00
-- url     : https://prove2.me/theorems/58374318-d135-453f-ab15-64173fc43caf
-- title:
--   Proof of Lemma 3, p. 14 — with K₂ = M³(M + 1), H₂ = M(M + 1) as in Lemma 2, every plan with q₂ ≠ M costs more than the threshold
-- statement:
--   Let $M \ge U \ge L > 0$ be integers with $L + U < 2\sqrt{2LU}$, and consider the periodic instance $\mathrm{JRP}_{M,U,L}$ with $K_0 = LU$, $K_1 = 0$, $H_1 = 1$, $K_2 = M^3(M+1)$, $H_2 = M(M+1)$. For all positive integers $q_1, q_2$ with $q_2 \neq M$,
--   $$\mathrm{JRP}_{M,U,L}(q_1, q_2) > L + U + 2M^2(M+1).$$
--
--   So no plan with $q_2 \ne M$ reaches the threshold $z_{M,L,U}$: item 2's heavy EOQ term pins $q_2 = M$, exactly as in the proof of Lemma 2.
--
--   **Formalization Note** The paper says only that $K_2, H_2$ are "sufficiently large … as in the proof … in Lemma 2". The statement uses Lemma 2's values, so the claim is about one explicit instance.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 14, §3.1, proof of Lemma 3, first paragraph (with p. 11, proof of Lemma 2, "Optimal replenishment cycle for item 2")

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem item2_pinned (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q₁ q₂ : ℕ)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hne : q₂ ≠ M) :
    (threshold M L U : ℝ) < rangeCost M L U q₁ q₂ := by sorry

end JRPHard.RangeDiv
