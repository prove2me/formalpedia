-- Prove2me | Theorems.Thm_JRPHard_Periodic_reduction_to_4
-- name    : JRPHard.Periodic.reduction_to_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:30.44529+00:00
-- url     : https://prove2.me/theorems/950673cd-ca55-47c0-a430-6a4034121904
-- title:
--   Proof of Lemma 2, p. 11 — with q₂ = M the instance reduces to problem (4): JRP(q₁, M) = EOQ_{K₂,H₂}(M) + M/gcd(q₁, M) + q₁
-- statement:
--   Let $M$ be a natural number and $q_1$ a positive integer. For the periodic JRP instance of Lemma 2 ($K_0 = M$, $K_1 = 0$, $H_1 = 1$, $H_2 = M(M+1)$, $K_2 = M^3(M+1)$), fixing item 2's period at $q_2 = M$ gives
--   $$\mathrm{JRP}_M(q_1, M) = \mathrm{EOQ}_2(M) + \frac{M}{\gcd(q_1,M)} + q_1 .$$
--
--   Since $\mathrm{EOQ}_2(M)$ does not depend on $q_1$, minimizing the instance over $q_1$ with $q_2 = M$ is exactly problem (4).
--
--   **Formalization Note** The identity holds for every natural number $M$; the paper's context is an odd composite $M$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 11, §2.2, proof of Lemma 2, "Optimal replenishment cycle for item 1", first sentence; problem (4)

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem reduction_to_4 (M q₁ : ℕ) (hq₁ : 0 < q₁) :
    lemma2Cost M q₁ M = eoq2 M M + obj4 M q₁ := by sorry

end JRPHard.Periodic
