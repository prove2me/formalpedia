-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_discrete_min_closure
-- name    : MatrixAnalytic.PH.discrete_min_closure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:50.58435+00:00
-- url     : https://prove2.me/theorems/1e3ae4e5-2426-415a-b546-8dce34bb24fa
-- title:
--   Theorem 2.6.4 — the minimum of independent PH_d variables is PH_d$(\tau\otimes\beta, T\otimes S)$
-- statement:
--   Let $X$ be $\mathrm{PH}_d(\boldsymbol\tau, T)$ with $n$ phases and $Y$ be $\mathrm{PH}_d(\boldsymbol\beta, S)$ with $m$ phases, independent. On the $nm$ phases $(i, j)$ define the Kronecker products
--   $$\boldsymbol\gamma = \boldsymbol\tau\otimes\boldsymbol\beta, \quad \gamma_{(i,j)} = \tau_i\beta_j, \qquad C = T\otimes S, \quad C_{(i,j),(r,k)} = T_{ir}S_{jk}.$$
--   Then $(\boldsymbol\gamma, C)$ is a discrete PH representation and $Z = \min(X, Y)$ is $\mathrm{PH}_d(\boldsymbol\gamma, C)$: for every $k \ge 0$,
--   $$\mathrm P_{(\boldsymbol\gamma, C)}[Z > k] = \mathrm P[X > k]\,\mathrm P[Y > k].$$
--
--   Hence the family of discrete PH distributions is closed under the minimum of independent variables.
--
--   **Formalization Note** The law of the minimum of independent variables is characterized by its survival function, the product of the two survival functions, which is how "$\min(X, Y)$ is $\mathrm{PH}_d(\boldsymbol\gamma, C)$" is stated; $\mathrm P[Z > k] = 1 - \mathrm P[Z \le k]$ with `dcdf` of `MatrixAnalytic.PH.Discrete`. The $nm$ phases are the product type `ι × κ` and $C$ is `Matrix.kronecker T S`.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 54, Theorem 2.6.4

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.6.4 (Latouche–Ramaswami, p. 54): if `X` is `PH_d(τ, T)` with `n` phases and `Y`,
independent of `X`, is `PH_d(β, S)` with `m` phases, then `Z = min(X, Y)` is `PH_d(γ, C)` with
`nm` phases, `γ = τ ⊗ β`, `C = T ⊗ S`. The law of the minimum of independent variables is
given by its survival function `P[Z > k] = P[X > k] P[Y > k]`. -/
theorem discrete_min_closure {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) :
    IsPHdRep (fun p : ι × κ => τ p.1 * β p.2) (Matrix.kronecker T S) ∧
    ∀ k : ℕ,
      1 - dcdf (fun p : ι × κ => τ p.1 * β p.2) (Matrix.kronecker T S) k =
        (1 - dcdf τ T k) * (1 - dcdf β S k) := by sorry

end MatrixAnalytic.PH
