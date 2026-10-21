-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_discrete_pmf_cdf_formula
-- name    : MatrixAnalytic.PH.discrete_pmf_cdf_formula
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:33.529709+00:00
-- url     : https://prove2.me/theorems/5ea7b088-96b2-46e1-bf39-d59a5a81b1e1
-- title:
--   Theorem 2.5.3 — $\mathrm P[X=0]=\tau_0$, $\mathrm P[X=k]=\tau T^{k-1}t$, $\mathrm P[X\le k]=1-\tau T^k\mathbf 1$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a discrete PH representation: $T \ge 0$ entrywise, $\boldsymbol t = \mathbf 1 - T\mathbf 1 \ge 0$, $\boldsymbol\tau \ge 0$ and $\tau_0 = 1 - \boldsymbol\tau\mathbf 1 \ge 0$. Let $X$ be the absorption time into $0$ of the chain with transition matrix $P = \begin{bmatrix} 1 & \mathbf 0 \\ \boldsymbol t & T\end{bmatrix}$ started with distribution $(\tau_0, \boldsymbol\tau)$. Then
--   $$\mathrm P[X = 0] = \tau_0, \qquad \mathrm P[X = k] = \boldsymbol\tau T^{k-1}\boldsymbol t \quad (k \ge 1), \qquad \mathrm P[X \le k] = 1 - \boldsymbol\tau T^k\mathbf 1 \quad (k \ge 0).$$
--
--   These formulas are the discrete analogue of Theorem 2.4.1 and the starting point for the generating function (2.14) and the factorial moments (2.15).
--
--   **Formalization Note** $\mathrm P[X \le k]$ and $\mathrm P[X = k]$ are the definitions `dcdf` and `dpmf` of `MatrixAnalytic.PH.Discrete`, computed from the powers $P^k$ of the full transition matrix; they are not defined by these formulas. $k - 1$ is natural-number subtraction, used only for $k \ge 1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 49, Theorem 2.5.3

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.5.3 (Latouche–Ramaswami, p. 49): if `X` is `PH_d(τ, T)` then `P[X = 0] = τ₀`,
`P[X = k] = τ T^{k−1} t` for `k ≥ 1`, and `P[X ≤ k] = 1 − τ T^k 𝟙` for `k ≥ 0`, where
`τ₀ = 1 − τ𝟙` and `t = 𝟙 − T𝟙`. -/
theorem discrete_pmf_cdf_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHdRep τ T) :
    dpmf τ T 0 = dInitAtom τ ∧
    (∀ k : ℕ, 1 ≤ k → dpmf τ T k = τ ⬝ᵥ ((T ^ (k - 1)) *ᵥ dExitProbs T)) ∧
    (∀ k : ℕ, dcdf τ T k = 1 - τ ⬝ᵥ ((T ^ k) *ᵥ fun _ => (1 : ℝ))) := by sorry

end MatrixAnalytic.PH
