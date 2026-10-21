-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_marginal_stack_size
-- name    : MatrixAnalytic.Tree.marginal_stack_size
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:07.423957+00:00
-- url     : https://prove2.me/theorems/ba617ab4-f2de-4d57-91c9-7487630cf876
-- title:
--   Corollary 14.3.2 — p₁ = π₀aN and p_n = π₁R^{n−1} (π₁ the level-1 vector p₁)
-- statement:
--   Let $Q$ be the irreducible generator of a tree process with data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$, let $N$ be its expected-time matrix and $R = \sum_{1 \le i \le m} R(i) = \big(\sum_{1 \le i \le m} A_i\big) N$. Assume the process is positive recurrent with stationary probability vector $\pi$, and let $p_{n,j}$ be the stationary probability that the stack size is $n$ and the phase at the top is $j$. Then
--
--   $$\boldsymbol p_1 = \pi_0 \boldsymbol a N \qquad\text{and}\qquad \boldsymbol p_n = \pi_1 R^{n-1} \quad\text{for } n \ge 1 .$$
--
--   This is Corollary 14.3.2. The printed $\pi_1$ is the stationary vector of level 1 (the stacks of size one, the node $s\{\cdot\}$), as $\pi_0$ is the stationary probability of level 0 (the empty stack); the statement's own case $n = 1$ reads $\boldsymbol p_1 = \pi_1$, so $\pi_1 = \boldsymbol p_1$.
--
--   **Formalization Note** $\pi_1$ is formalized as $\boldsymbol p_1$ (see above; the book never uses a subscript for node subvectors, which it writes $\pi\{\cdot\}$ with braces, and the alternative reading $\pi\{1\}$ would contradict the corollary's own first line at $n = 1$, finding F1). $p_{n,j}$ is the sum of $\pi$ over the stacks of length $n$ with top $j$; the identities are coordinatewise in $[0, \infty]$, with $R^0 = I$ and $n - 1$ evaluated only for $n \ge 1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 291, Corollary 14.3.2

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Corollary 14.3.2, p. 291: if the process is positive recurrent, `p₁ = π₀ a N` and
`p_n = π₁ R^{n−1}` for `n ≥ 1`, where `R = Σ_i R(i) = (Σ_i A_i) N` and `p_{n,j}` is the
stationary probability that the stack size is `n` and the top index is `j`. The printed `π₁` is
the stationary vector of level 1 (stack size 1, the node `s{·}`), as `π₀` is that of level 0:
the statement's own case `n = 1` reads `p₁ = π₁`, so `π₁ = p₁` here. -/
theorem marginal_stack_size {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) :
    (∀ j : ι, ENNReal.ofReal (stackMarginal π 1 j) = vecMulE (rootVec T π) (matN T) j) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ j : ι,
        ENNReal.ofReal (stackMarginal π n j) =
          vecMulE (fun k => ENNReal.ofReal (stackMarginal π 1 k)) (matPowE (matR T) (n - 1)) j := by sorry

end MatrixAnalytic.Tree
