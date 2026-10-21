-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_eq_6
-- name    : NetworkVolatility.Robust.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:20.620464+00:00
-- url     : https://prove2.me/theorems/7fb227f6-dd5b-415a-9d0a-1be91def0dc5
-- title:
--   Eq. (6), p. 14 — $\|I-(I-\alpha W)(I-\alpha\tilde W)^{-1}\|_2\le\alpha\lambda_{\max}\epsilon/(1-\alpha\lambda_{\max}(1+\epsilon))$
-- statement:
--   Assume the standing assumptions ($\alpha\ge0$, $W\ge0$, $W$ symmetric with zero diagonal), $\epsilon\ge0$, and condition (1), $\alpha\lambda_{\max}(1+\epsilon)<1$. Then for every $\tilde W\in\mathcal W(W,\epsilon)$, with $M=I-(I-\alpha W)(I-\alpha\tilde W)^{-1}$,
--   $$\|M\|_2\le\frac{\alpha\lambda_{\max}\epsilon}{1-\alpha\lambda_{\max}(1+\epsilon)} .$$
--
--   Since every eigenvalue of $M$ is at most $\|M\|_2$ in absolute value, this bound with Steps 1–3 gives the upper-bound half of Theorem 1.
--
--   **Formalization Note** $\|\cdot\|_2$ is the spectral norm (Mathlib's scoped $\ell_2$ operator norm on matrices).
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 14, eq. (6), proof of Theorem 1, Part 3, Step 4

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open scoped Matrix.Norms.L2Operator

/-- Eq. (6), proof of Theorem 1, Part 3, Step 4, p. 14. Under the standing assumptions, `ε ≥ 0` and
condition (1), every `W̃ ∈ 𝒲(W, ε)` satisfies, in the spectral norm,
`‖I - (I - αW)(I - αW̃)⁻¹‖₂ ≤ αλmaxε / (1 - αλmax(1 + ε))`. -/
theorem eq_6 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α ε : ℝ)
    (hS : Standing W α) (hε : 0 ≤ ε) (h1 : α * lamMax W * (1 + ε) < 1)
    (Wt : Matrix (Fin n) (Fin n) ℝ) (hWt : Wt ∈ uncSet W ε) :
    ‖1 - (1 - α • W) * (1 - α • Wt)⁻¹‖ ≤ α * lamMax W * ε / (1 - α * lamMax W * (1 + ε)) := by sorry

end NetworkVolatility.Robust
