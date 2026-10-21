-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_discrete_convolution_closure
-- name    : MatrixAnalytic.PH.discrete_convolution_closure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:28.263223+00:00
-- url     : https://prove2.me/theorems/a8537a51-6d08-485d-b74c-8899203f64c8
-- title:
--   Theorem 2.6.1 — the sum of independent PH_d variables is PH_d$([\tau, \tau_0\beta], [[T, t\cdot\beta],[0, S]])$
-- statement:
--   Let $X$ be $\mathrm{PH}_d(\boldsymbol\tau, T)$ with $n$ phases and $Y$ be $\mathrm{PH}_d(\boldsymbol\beta, S)$ with $m$ phases, independent; write $\boldsymbol t = \mathbf 1 - T\mathbf 1$ and $\tau_0 = 1 - \boldsymbol\tau\mathbf 1$. Define, on the $n + m$ phases (the phases of $X$ followed by those of $Y$),
--   $$\boldsymbol\gamma = [\boldsymbol\tau, \tau_0\boldsymbol\beta], \qquad C = \begin{bmatrix} T & \boldsymbol t\cdot\boldsymbol\beta \\ 0 & S\end{bmatrix}, \qquad (\boldsymbol t\cdot\boldsymbol\beta)_{ij} = t_i\beta_j.$$
--   Then $(\boldsymbol\gamma, C)$ is a discrete PH representation and $X + Y$ is $\mathrm{PH}_d(\boldsymbol\gamma, C)$: for every $k \ge 0$,
--   $$\mathrm P_{(\boldsymbol\gamma, C)}[Z = k] = \sum_{a=0}^{k} \mathrm P[X = a]\,\mathrm P[Y = k - a].$$
--
--   Hence the family of discrete PH distributions is closed under convolution.
--
--   **Formalization Note** The law of the sum of independent variables is the convolution of their probability mass functions, which is how "$X + Y$ is $\mathrm{PH}_d(\boldsymbol\gamma, C)$" is stated; no probability space is introduced. The $n + m$ phases are the sum type `ι ⊕ κ` and $C$ is `Matrix.fromBlocks`. The conclusion also asserts that $(\boldsymbol\gamma, C)$ satisfies the conditions of a discrete PH representation.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 51, Theorem 2.6.1

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Discrete

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.6.1 (Latouche–Ramaswami, p. 51): if `X` is `PH_d(τ, T)` with `n` phases and `Y`,
independent of `X`, is `PH_d(β, S)` with `m` phases, then `X + Y` is `PH_d(γ, C)` with `n + m`
phases, `γ = [τ, τ₀β]`, `C = [[T, t·β], [0, S]]`, `(t·β)_ij = t_i β_j`. The law of the
independent sum is the convolution of the two probability mass functions,
`P[X + Y = k] = Σ_{a=0}^{k} P[X = a] P[Y = k − a]`. -/
theorem discrete_convolution_closure {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (β : κ → ℝ) (S : Matrix κ κ ℝ)
    (hX : IsPHdRep τ T) (hY : IsPHdRep β S) :
    IsPHdRep (Sum.elim τ (dInitAtom τ • β)) (Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) ∧
    ∀ k : ℕ,
      dpmf (Sum.elim τ (dInitAtom τ • β)) (Matrix.fromBlocks T (vecMulVec (dExitProbs T) β) 0 S) k =
        ∑ a ∈ Finset.range (k + 1), dpmf τ T a * dpmf β S (k - a) := by sorry

end MatrixAnalytic.PH
