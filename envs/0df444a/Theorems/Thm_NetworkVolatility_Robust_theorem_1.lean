-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_theorem_1
-- name    : NetworkVolatility.Robust.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:27.45024+00:00
-- url     : https://prove2.me/theorems/6c731295-10b1-48e4-a7ae-17450e21b4be
-- title:
--   Theorem 1, p. 11 — interior equilibria on $\mathcal W(W,\epsilon)$ and $\mathrm{RV}(W,\epsilon)=\alpha\lambda_{\max}\epsilon/(1-\alpha\lambda_{\max}(1+\epsilon))$
-- statement:
--   A monopolist sells a divisible good to $n$ agents on a network $W$ (non-negative, symmetric, zero diagonal) with network-effect strength $\alpha\ge0$ and marginal cost $c$. The seller fixes prices $p$ ex ante, and the agents then play the consumption equilibrium of the game on the realized network. Suppose Assumption 1 holds ($\alpha\sum_jW_{ij}<1$ for all $i$), let $\lambda_{\max}=\lambda_{\max}(W)$, and let $\epsilon\ge0$ satisfy condition (1),
--   $$\epsilon<\frac{1}{\alpha\lambda_{\max}}-1\qquad(\text{written } \alpha\lambda_{\max}(1+\epsilon)<1).$$
--   Then:
--
--   1. for every $\tilde W\in\mathcal W(W,\epsilon)$ and every $b>c\mathbf 1$, the seller has an optimal price vector for the forecast network $W$, and at every such price the consumption game on $\tilde W$ has an **interior** consumption equilibrium ($\tilde x_i>0$ for all $i$);
--   2. the revenue volatility, the least upper bound of the relative revenue changes $|R(W,\alpha,b)-R(\tilde W,\alpha,b)|/R(W,\alpha,b)$ over $\tilde W\in\mathcal W(W,\epsilon)$ and $b>c\mathbf 1$, is
--   $$\mathrm{RV}(W,\epsilon)=\frac{\alpha\lambda_{\max}\epsilon}{1-\alpha\lambda_{\max}(1+\epsilon)} .$$
--
--   Here $R(W,\alpha,b)$ is the seller's optimal revenue in the game on $W$, and $R(\tilde W,\alpha,b)$ is the revenue at that same ex-ante optimal price with the agents' equilibrium on $\tilde W$. The result says that the worst-case relative revenue loss or gain from misjudging the network by $\epsilon$ in spectral norm depends on the network only through its largest eigenvalue.
--
--   **Formalization Note** Added to the page: $\epsilon\ge0$ (for $\epsilon<0$ the set $\mathcal W(W,\epsilon)$ is empty when $W\neq0$), the zero diagonal of $W$ and of every $\tilde W$ (the utility sums over $j\ne i$), and $\mathrm{RV}$ as a least upper bound instead of a maximum (the paper's extremal $b=c\mathbf 1+v_{\max}$ satisfies $b>c\mathbf 1$ only when the top eigenvector is strictly positive). The revenues are defined from the game itself, not from the closed form of Proposition 2.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 11, Theorem 1 (proof pp. 11–14)

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

/-- Theorem 1, p. 11. Under the standing assumptions, Assumption 1, `ε ≥ 0` and condition (1)
`αλmax(1 + ε) < 1` (i.e. `ε < 1/(αλmax) - 1`):
(a) for every `W̃ ∈ 𝒲(W, ε)` and every `b > c1`, the seller has an optimal price for `W`, and at
every such price the consumption game on `W̃` has an interior (strictly positive) equilibrium;
(b) the revenue volatility `RV(W, ε)`, the least upper bound of the relative revenue changes, equals
`αλmaxε / (1 - αλmax(1 + ε))`. -/
theorem theorem_1 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α c ε : ℝ)
    (hS : Standing W α) (hA1 : Assumption1 W α) (hε : 0 ≤ ε)
    (h1 : α * lamMax W * (1 + ε) < 1) :
    (∀ Wt ∈ uncSet W ε, ∀ b : Fin n → ℝ, Assumption2 b c →
      (∃ p, IsOptimalPrice W α b c p) ∧
      ∀ p, IsOptimalPrice W α b c p →
        ∃ x : Fin n → ℝ, IsConsumptionEq Wt α b p x ∧ ∀ i, 0 < x i) ∧
    IsLUB (volatilitySet W α c ε) (α * lamMax W * ε / (1 - α * lamMax W * (1 + ε))) := by sorry

end NetworkVolatility.Robust
