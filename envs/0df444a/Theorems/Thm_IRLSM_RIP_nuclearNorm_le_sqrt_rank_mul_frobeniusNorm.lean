-- Prove2me | Theorems.Thm_IRLSM_RIP_nuclearNorm_le_sqrt_rank_mul_frobeniusNorm
-- name    : IRLSM.RIP.nuclearNorm_le_sqrt_rank_mul_frobeniusNorm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:32.230976+00:00
-- url     : https://prove2.me/theorems/4f1c8aad-392d-43be-995f-dae6cc0b4dd3
-- title:
--   Proof of Proposition 6.8, p. 19 — ‖H‖_* ≤ √r‖H‖_F for rank H ≤ r
-- statement:
--   Let $H$ be a real $n\times p$ matrix of rank at most $r$. Then
--   $$
--   \|H\|_* \le \sqrt r\,\|H\|_F .
--   $$
--
--   In the proof of Proposition 6.8 it is applied with $r = 2k$ to $H_0$, giving $\|H_0\|_* \le \sqrt{2k}\,\|H_0\|_F$.
--
--   **Formalization Note.** Real matrices; $\|\cdot\|_*$ is the sum of the singular values and $\|\cdot\|_F$ the entrywise Euclidean norm.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Proposition 6.8, p. 19, first inequality of ‖H0‖_* ≤ √(2k)‖H0‖_F ≤ √(2k)‖H0 + H1‖

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- For a matrix of rank at most `r`, `‖H‖_* ≤ √r ‖H‖_F`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Proposition 6.8, p. 19 (first inequality of
"‖H₀‖_* ≤ √(2k)‖H₀‖_F ≤ √(2k)‖H₀ + H₁‖", stated for a general rank bound `r`).

Formalization Note: real matrices; `nuclearNorm` and `frobeniusNorm` from the published Core
module. -/
theorem nuclearNorm_le_sqrt_rank_mul_frobeniusNorm {n p : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (r : ℕ) (hr : H.rank ≤ r) :
    nuclearNorm H ≤ Real.sqrt r * frobeniusNorm H := by sorry

end IRLSM.RIP
