-- Prove2me | Theorems.Thm_IRLSM_RIP_frobeniusNorm_le_of_traceInner_eq_zero
-- name    : IRLSM.RIP.frobeniusNorm_le_of_traceInner_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:44.842601+00:00
-- url     : https://prove2.me/theorems/b6987b8c-60a6-4241-8851-674d3db34c71
-- title:
--   Proof of Proposition 6.8, p. 19 — ‖H‖_F ≤ ‖H + K‖_F when ⟨H, K⟩ = 0
-- statement:
--   Let $H, K$ be real $n\times p$ matrices with $\langle H, K\rangle = \operatorname{Tr}(HK^{\top}) = 0$. Then
--   $$
--   \|H\|_F \le \|H + K\|_F .
--   $$
--
--   In the proof of Proposition 6.8 this is the step $\|H_0\|_F \le \|H_0 + H_1\|_F$, "by orthogonality of $H_0$ and $H_1$".
--
--   **Formalization Note.** The page writes $\|H_0 + H_1\|$ for the Frobenius norm $\|H_0 + H_1\|_F$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Proposition 6.8, p. 19, second inequality of ‖H0‖_* ≤ √(2k)‖H0‖_F ≤ √(2k)‖H0 + H1‖

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- If `⟨H, K⟩ = 0` then `‖H‖_F ≤ ‖H + K‖_F`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Proposition 6.8, p. 19 (second inequality of
"‖H₀‖_* ≤ √(2k)‖H₀‖_F ≤ √(2k)‖H₀ + H₁‖ by orthogonality of H₀ and H₁"; the page writes
`‖H₀ + H₁‖` for the Frobenius norm).

Formalization Note: real matrices; `⟨·,·⟩` is `traceInner`. -/
theorem frobeniusNorm_le_of_traceInner_eq_zero {n p : ℕ} (H K : Matrix (Fin n) (Fin p) ℝ)
    (h : traceInner H K = 0) :
    frobeniusNorm H ≤ frobeniusNorm (H + K) := by sorry

end IRLSM.RIP
