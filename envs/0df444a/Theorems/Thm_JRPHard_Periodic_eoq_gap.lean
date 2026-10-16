-- Prove2me | Theorems.Thm_JRPHard_Periodic_eoq_gap
-- name    : JRPHard.Periodic.eoq_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:32.173624+00:00
-- url     : https://prove2.me/theorems/f14b9820-ca33-4be3-9632-c736d4e2a748
-- title:
--   Proof of Lemma 2, p. 11 — for q₂ ≠ M, EOQ_{K₂,H₂}(q₂) ≥ EOQ_{K₂,H₂}(M ± 1) ≥ EOQ_{K₂,H₂}(M) + M
-- statement:
--   Let $M \ge 2$ be a natural number, $K_2 = M^3(M+1)$, $H_2 = M(M+1)$, and write $\mathrm{EOQ}_2(q) = K_2/q + H_2 q$. Then
--   $$\mathrm{EOQ}_2(M \pm 1) = \mathrm{EOQ}_2(M) + \frac{H_2}{M \pm 1} \ge \mathrm{EOQ}_2(M) + M,$$
--   and for every positive integer $q_2 \neq M$,
--   $$\mathrm{EOQ}_2(q_2) \ge \mathrm{EOQ}_2(M) + M.$$
--
--   The EOQ cost of item 2 is minimized at $q_2 = M$, and any other period costs at least $M$ more. This is the first step in showing that every optimal solution of the Lemma 2 instance has $q_2 = M$.
--
--   **Formalization Note** The two identities at $M+1$ and $M-1$ and the two bounds $H_2/(M\pm1) \ge M$ are stated separately. The paper states the step "for any $q_2 \ne M$" for odd composite $M$; it holds for every $M \ge 2$, which is the hypothesis here ($M - 1 \ge 1$ is needed for $\mathrm{EOQ}_2(M-1)$ to be a positive period).
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 11, §2.2, proof of Lemma 2, "Optimal replenishment cycle for item 2" (displayed inequality)

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem eoq_gap (M : ℕ) (hM : 2 ≤ M) :
    eoq2 M (M + 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) + 1) ∧
    eoq2 M (M - 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) - 1) ∧
    (M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) + 1) ∧
    (M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) - 1) ∧
    ∀ q₂ : ℕ, 0 < q₂ → q₂ ≠ M → eoq2 M M + (M : ℝ) ≤ eoq2 M q₂ := by sorry

end JRPHard.Periodic
