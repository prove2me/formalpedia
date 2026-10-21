-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_theorem_1_part_1
-- name    : NetworkVolatility.Robust.theorem_1_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:59.551299+00:00
-- url     : https://prove2.me/theorems/f57a4ff6-3f34-4356-9825-4b92fbb1ccc2
-- title:
--   Proof of Theorem 1, Part 1, pp. 11–12 — for $\tilde W\in\mathcal W(W,\epsilon)$, $\rho(\alpha\tilde W)<1$ and $(I-\alpha\tilde W)^{-1}$ exists and is non-negative
-- statement:
--   Assume the standing assumptions ($\alpha\ge0$, $W\ge0$, $W$ symmetric with zero diagonal), $\epsilon\ge0$, and condition (1) of Theorem 1, $\alpha\lambda_{\max}(1+\epsilon)<1$. Then every $\tilde W\in\mathcal W(W,\epsilon)$ satisfies
--   $$\rho(\alpha\tilde W)<1,\qquad \alpha\|\tilde W\|_2<1,$$
--   the matrix $I-\alpha\tilde W$ is non-singular, and $(I-\alpha\tilde W)^{-1}$ is entrywise non-negative.
--
--   This is the first part of the proof of Theorem 1: it is what makes the consumption game on the realized network well behaved even though $\tilde W$ need not satisfy Assumption 1.
--
--   **Formalization Note** Condition (1), printed as $\epsilon<1/(\alpha\lambda_{\max})-1$, is written multiplied out, $\alpha\lambda_{\max}(1+\epsilon)<1$; the two agree when $\alpha\lambda_{\max}>0$, and the multiplied form avoids the convention $1/0=0$. The page announces $\rho(\alpha\tilde W)\le1$ and then proves the strict inequality; the strict form is stated.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), pp. 11–12, proof of Theorem 1, Part 1

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open scoped Matrix.Norms.L2Operator

/-- Proof of Theorem 1, Part 1, pp. 11–12. Under the standing assumptions, `ε ≥ 0` and condition (1)
`αλmax(1 + ε) < 1`, every `W̃ ∈ 𝒲(W, ε)` has `ρ(αW̃) < 1` and `α‖W̃‖₂ < 1`, `I - αW̃` is
non-singular, and `(I - αW̃)⁻¹` is entrywise non-negative. -/
theorem theorem_1_part_1 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α ε : ℝ)
    (hS : Standing W α) (hε : 0 ≤ ε) (h1 : α * lamMax W * (1 + ε) < 1)
    (Wt : Matrix (Fin n) (Fin n) ℝ) (hWt : Wt ∈ uncSet W ε) :
    specRadius (α • Wt) < 1 ∧ α * ‖Wt‖ < 1 ∧ IsUnit (1 - α • Wt) ∧
      ∀ i j, 0 ≤ (1 - α • Wt)⁻¹ i j := by sorry

end NetworkVolatility.Robust
