-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_eoq_shift
-- name    : JRPHard.Aperiodic.eoq_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:15.925758+00:00
-- url     : https://prove2.me/theorems/cd32b30f-4bd6-42b8-b354-4fd2f5e7657c
-- title:
--   Proof of Lemma 1, p. 9 — EOQ_{K₂,H₂}(M ± 1) = EOQ_{K₂,H₂}(M) + H₂/(M ± 1) ≥ EOQ_{K₂,H₂}(M) + K₀
-- statement:
--   Let $M \ge 2$ be an integer and consider item 2 of the instance of Lemma 1, with $K_2 = M^3(M^2-1)$ and $H_2 = M(M^2-1)$, and the discount $K_0 = M(M-1)$. Moving item 2's cycle one step away from $M$ in either direction costs exactly $H_2/(M\pm1)$, and this is at least the discount $K_0$:
--   $$\mathrm{EOQ}_{K_2,H_2}(M \pm 1) = \mathrm{EOQ}_{K_2,H_2}(M) + \frac{H_2}{M \pm 1} \ \ge\ \mathrm{EOQ}_{K_2,H_2}(M) + K_0 .$$
--   Both signs are asserted: the identity for $M+1$ and for $M-1$, and each added term is at least $K_0$.
--
--   This is the computation that makes item 2's period rigid: no saving on the discount can pay for moving $q_2$ away from $M$.
--
--   **Formalization Note** The cycle $M-1$ is the natural-number $M-1$, which equals the real $M-1$ because $M \ge 2$; the divisor $M-1$ on the right is real subtraction.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 9, proof of Lemma 1, "Optimal replenishment cycle for item 2", second display

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem eoq_shift (M : ℕ) (hM : 2 ≤ M) :
    (eoq2 M (M + 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) + 1) ∧
      (coefK0 M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) + 1)) ∧
    (eoq2 M (M - 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) - 1) ∧
      (coefK0 M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) - 1)) := by sorry

end JRPHard.Aperiodic
