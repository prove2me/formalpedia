-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_cdf_density_formula
-- name    : MatrixAnalytic.PH.cdf_density_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:01.325036+00:00
-- url     : https://prove2.me/theorems/6ae9ef63-bf6f-427e-91e4-949ceaac8901
-- title:
--   Theorem 2.4.1 — $F(x) = 1 - \tau\exp(Tx)\mathbf 1$ and $f(x) = \tau\exp(Tx)t$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a continuous PH representation: $T$ satisfies (2.4) with exit vector $\boldsymbol t = -T\mathbf 1 \ge 0$, and $(\tau_0, \boldsymbol\tau)$, $\tau_0 = 1 - \boldsymbol\tau\mathbf 1$, is a probability vector. Let $X$ be the time until absorption into state $0$ of the Markov process with generator $Q = \begin{bmatrix} 0 & \mathbf 0 \\ \boldsymbol t & T\end{bmatrix}$ and initial distribution $(\tau_0, \boldsymbol\tau)$, and let $F(x) = \mathrm P[X \le x] = \mathrm P[J(x) = 0]$ be its distribution function, computed from the transition function $\exp(Qx)$. Then
--   $$F(x) = 1 - \boldsymbol\tau\exp(Tx)\mathbf 1 \quad \text{for } x \ge 0, \qquad\qquad f(x) = F'(x) = \boldsymbol\tau\exp(Tx)\boldsymbol t \quad \text{for } x > 0.$$
--
--   This is the basic formula that makes PH distributions computable: the law of $X$ is expressed through the exponential of the $n \times n$ block $T$ alone, without the absorbing state.
--
--   **Formalization Note** $F$ is the definition `cdf` of `MatrixAnalytic.PH.Continuous`, i.e. $\sum_a (\tau_0, \boldsymbol\tau)_a \exp(Qx)_{a0}$; it is not defined by the formula of the theorem. The density claim is stated as `HasDerivAt` of $F$ at every $x > 0$ (at $x = 0$ the distribution may have the atom $\tau_0$). Phases form an arbitrary finite type.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 41, Theorem 2.4.1, Eqs. (2.7)–(2.8)

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.4.1 (Latouche–Ramaswami, p. 41): if `X` is `PH(τ, T)`, its distribution function is
`F(x) = 1 − τ exp(Tx) 𝟙` for `x ≥ 0` (2.7) and its density is `f(x) = τ exp(Tx) t` for `x > 0`
(2.8), where `t = −T𝟙`. -/
theorem cdf_density_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) :
    (∀ x : ℝ, 0 ≤ x →
      cdf τ T x = 1 - τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ))) ∧
    (∀ x : ℝ, 0 < x →
      HasDerivAt (cdf τ T) (τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ exitRates T)) x) := by sorry

end MatrixAnalytic.PH
