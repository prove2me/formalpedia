-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_proposition_1
-- name    : NetworkVolatility.Robust.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:03.353068+00:00
-- url     : https://prove2.me/theorems/b17a9e1a-ed5b-4ad2-8ef9-f8f1a975e089
-- title:
--   Proposition 1, p. 8 — the consumption game is an exact potential game with a unique equilibrium, equal to $(I-\alpha W)^{-1}(b-p)>0$ when $b>p$
-- statement:
--   Assume the standing assumptions ($\alpha\ge0$, $W\ge0$ entrywise, $W$ symmetric with zero diagonal) and Assumption 1 ($\alpha\sum_jW_{ij}<1$ for all $i$). Fix primary values $b\in\mathbb R^n$ and prices $p\in\mathbb R^n$, and consider the consumption game $(W,\alpha,b,p)$ with utilities $u_i(x;W,b,p)=-\tfrac12x_i^2+b_ix_i+\alpha\sum_{j\ne i}W_{ij}x_ix_j-p_ix_i$ on strategy sets $\mathbb R_+$. Then:
--
--   1. the game is an **exact potential game**: there is $\Phi:\mathbb R^n\to\mathbb R$ such that for every profile $x\ge0$, agent $i$ and $y\ge0$,
--   $$\Phi(y,x_{-i})-\Phi(x)=u_i(y,x_{-i};W,b,p)-u_i(x;W,b,p);$$
--   2. the game has **exactly one** consumption equilibrium;
--   3. if $b>p$ (entrywise), then $I-\alpha W$ is invertible, and the equilibrium is strictly positive and equals
--   $$x(W,\alpha,b,p)=(I-\alpha W)^{-1}(b-p).$$
--
--   The closed form is what turns the seller's problem into a quadratic optimization in Proposition 2.
--
--   **Formalization Note** The page also says that the myopic best response converges to the equilibrium; that dynamic claim is not used by Theorem 1 and is not stated here. The zero diagonal of $W$ is needed for the closed form, because the utility sums over $j\neq i$ only.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 8, Proposition 1 (proof pp. 34–35)

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open Matrix

/-- Proposition 1 (The Consumption Game; Candogan et al. 2012), p. 8. Under the standing
assumptions and Assumption 1, for every price vector `p`:
the consumption game `(W, α, b, p)` is an exact potential game on `ℝ₊ⁿ`; it has exactly one
consumption equilibrium; and if `b > p`, then `I - αW` is invertible and the equilibrium is the
strictly positive vector `(I - αW)⁻¹ (b - p)`. -/
theorem proposition_1 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p : Fin n → ℝ)
    (hS : Standing W α) (hA1 : Assumption1 W α) :
    (∃ Φ : (Fin n → ℝ) → ℝ, ∀ (x : Fin n → ℝ) (i : Fin n) (y : ℝ), (∀ j, 0 ≤ x j) → 0 ≤ y →
        Φ (Function.update x i y) - Φ x =
          utility W α b p (Function.update x i y) i - utility W α b p x i) ∧
    (∃! x : Fin n → ℝ, IsConsumptionEq W α b p x) ∧
    ((∀ i, p i < b i) →
      IsUnit (1 - α • W) ∧ IsConsumptionEq W α b p ((1 - α • W)⁻¹ *ᵥ (b - p)) ∧
        ∀ i, 0 < ((1 - α • W)⁻¹ *ᵥ (b - p)) i) := by sorry

end NetworkVolatility.Robust
