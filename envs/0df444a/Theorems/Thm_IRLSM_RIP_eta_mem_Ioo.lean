-- Prove2me | Theorems.Thm_IRLSM_RIP_eta_mem_Ioo
-- name    : IRLSM.RIP.eta_mem_Ioo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:45:43.846956+00:00
-- url     : https://prove2.me/theorems/61d5c079-725e-44b8-a3b0-105921017180
-- title:
--   Proposition 6.8, pp. 18 and 20 — η = √2 δ_4k/(1 − δ_3k) ∈ (0, 1) when 0 < δ_4k < √2 − 1
-- statement:
--   Let $\mathcal S : \mathbb R^{n\times p}\to\mathbb R^m$ be linear with $0 < \delta_{4k} < \sqrt 2 - 1$. Then
--   $$
--   \eta = \sqrt 2\,\frac{\delta_{4k}}{1 - \delta_{3k}} \in (0,1) .
--   $$
--
--   This is the claim "$\eta \in (0,1)$" of Proposition 6.8, which the end of its proof derives from $\delta_{3k} \le \delta_{4k}$.
--
--   **Formalization Note.** $0 < \delta_{4k}$ is the positivity $\delta_k > 0$ of Definition 1.1.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Proposition 6.8, p. 18, and the last sentence of its proof, p. 20

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- If `0 < δ_{4k} < √2 − 1` then `η = √2 δ_{4k}/(1 − δ_{3k}) ∈ (0, 1)`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Proposition 6.8, p. 18 ("η ∈ (0, 1)") and the end of
its proof, p. 20 ("Since δ_3k ≤ δ_4k, we have η < 1 if δ_4k < √2 − 1").

Formalization Note: `0 < δ_{4k}` is the positivity "δ_k > 0" of Definition 1.1. -/
theorem eta_mem_Ioo {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < IRLSM.Convergence.ripConst A (4 * k)) (h66 : IRLSM.Convergence.ripConst A (4 * k) < Real.sqrt 2 - 1) :
    0 < Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k)) ∧
      Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k)) < 1 := by sorry

end IRLSM.RIP
