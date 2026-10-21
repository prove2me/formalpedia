-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_proposition_2
-- name    : NetworkVolatility.Robust.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:40.641432+00:00
-- url     : https://prove2.me/theorems/3a2f1e0a-7bc1-4f1e-921a-1ef8d04df5db
-- title:
--   Proposition 2, p. 9 — optimal price $(b+c\mathbf 1)/2$, consumption $(I-\alpha W)^{-1}(b-c\mathbf 1)/2$, revenue $((b-c\mathbf 1)/2)^\top(I-\alpha W)^{-1}((b-c\mathbf 1)/2)$
-- statement:
--   Assume the standing assumptions, Assumption 1 and Assumption 2 ($b>c\mathbf 1$). In the pricing–consumption game $(W,\alpha,b)$, where the seller chooses any $p\in\mathbb R^n$ and the agents then play a consumption equilibrium $x$, earning the seller $\sum_i(p_i-c)x_i$:
--
--   1. at the price $p^*=\frac{b+c\mathbf 1}{2}$, the profile $x^*=(I-\alpha W)^{-1}\frac{b-c\mathbf 1}{2}$ is a consumption equilibrium, and its revenue is the greatest achievable revenue;
--   2. the optimal revenue of the monopolist is
--   $$R(W,\alpha,b)=\Big(\frac{b-c\mathbf 1}{2}\Big)^{\!\top}(I-\alpha W)^{-1}\Big(\frac{b-c\mathbf 1}{2}\Big);$$
--   3. the equilibrium outcome is unique: any price $p'$ with a consumption equilibrium $x'$ attaining the greatest revenue has $(p',x')=(p^*,x^*)$.
--
--   Because the optimal price does not depend on $W$, a seller who fixes it ex ante keeps it when the realized network differs from the forecast, which is the premise of §3.
--
--   **Formalization Note** The optimal revenue $R(W,\alpha,b)$ is the supremum over all price vectors and their consumption equilibria; the theorem shows that this supremum is attained and computes it.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 9, Proposition 2 (proof p. 35)

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open Matrix

/-- Proposition 2 (The Pricing Consumption Game; Candogan et al. 2012), p. 9. Under the standing
assumptions and Assumptions 1 and 2, the price `p = (b + c1)/2` with consumption
`x = (I - αW)⁻¹ (b - c1)/2` is an equilibrium outcome of the two-stage game: `x` is a consumption
equilibrium at `p` and its revenue is the greatest achievable revenue; the optimal revenue is
`R(W, α, b) = ((b - c1)/2)ᵀ (I - αW)⁻¹ ((b - c1)/2)`; and every optimal outcome `(p', x')` equals
`(p, x)`. -/
theorem proposition_2 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ) (c : ℝ)
    (hS : Standing W α) (hA1 : Assumption1 W α) (hA2 : Assumption2 b c) :
    IsConsumptionEq W α b (fun i => (b i + c) / 2)
        ((1 - α • W)⁻¹ *ᵥ (fun i => (b i - c) / 2)) ∧
    IsGreatest (revenueSet W α b c)
        (revenue c (fun i => (b i + c) / 2) ((1 - α • W)⁻¹ *ᵥ (fun i => (b i - c) / 2))) ∧
    optRevenue W α b c =
        (fun i => (b i - c) / 2) ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ (fun i => (b i - c) / 2)) ∧
    (∀ p' x' : Fin n → ℝ, IsConsumptionEq W α b p' x' →
        IsGreatest (revenueSet W α b c) (revenue c p' x') →
        p' = (fun i => (b i + c) / 2) ∧ x' = (1 - α • W)⁻¹ *ᵥ (fun i => (b i - c) / 2)) := by sorry

end NetworkVolatility.Robust
