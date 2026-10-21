-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_discrete_mixture_closure
-- name    : MatrixAnalytic.PH.discrete_mixture_closure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:43.219283+00:00
-- url     : https://prove2.me/theorems/ed0b4575-bb2a-4bb9-a82c-0d72cfd5c6d1
-- title:
--   Theorem 2.6.2 — a convex mixture of PH_d distributions is PH_d$([\theta\tau, (1-\theta)\beta], \mathrm{diag}(T, S))$
-- statement:
--   Let $X$ be $\mathrm{PH}_d(\boldsymbol\tau, T)$ with $n$ phases and $Y$ be $\mathrm{PH}_d(\boldsymbol\beta, S)$ with $m$ phases, with distribution functions $F(k) = \mathrm P[X \le k]$ and $G(k) = \mathrm P[Y \le k]$. Let $0 \le \theta \le 1$ and define, on the $n + m$ phases,
--   $$\boldsymbol\gamma = [\theta\boldsymbol\tau, (1 - \theta)\boldsymbol\beta], \qquad C = \begin{bmatrix} T & 0 \\ 0 & S\end{bmatrix}.$$
--   Then $(\boldsymbol\gamma, C)$ is a discrete PH representation and its distribution function is the convex mixture
--   $$F_{(\boldsymbol\gamma, C)}(k) = \theta F(k) + (1 - \theta) G(k) \qquad \text{for all } k \ge 0.$$
--
--   Hence the family of discrete PH distributions is closed under finite convex mixtures.
--
--   **Formalization Note** The theorem is a statement about distribution functions, stated through the definition `dcdf` of `MatrixAnalytic.PH.Discrete`; no independence is involved. The $n + m$ phases are the sum type `ι ⊕ κ`.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 52, Theorem 2.6.2

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.6.2 (Latouche–Ramaswami, p. 52): if `X` is `PH_d(τ, T)` with `n` phases and `Y` is
`PH_d(β, S)` with `m` phases, with distribution functions `F` and `G`, then for `0 ≤ θ ≤ 1` the
convex mixture `θF + (1 − θ)G` is the distribution function of `PH_d(γ, C)` with `n + m` phases,
`γ = [θτ, (1 − θ)β]`, `C = [[T, 0], [0, S]]`. -/
theorem discrete_mixture_closure {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IsPHdRep (Sum.elim (θ • τ) ((1 - θ) • β)) (Matrix.fromBlocks T 0 0 S) ∧
    ∀ k : ℕ,
      dcdf (Sum.elim (θ • τ) ((1 - θ) • β)) (Matrix.fromBlocks T 0 0 S) k =
        θ * dcdf τ T k + (1 - θ) * dcdf β S k := by sorry

end MatrixAnalytic.PH
