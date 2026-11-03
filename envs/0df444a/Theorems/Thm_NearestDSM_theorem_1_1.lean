-- Prove2me | Theorems.Thm_NearestDSM_theorem_1_1
-- name    : NearestDSM.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:03.20024+00:00
-- url     : https://prove2.me/theorems/268474c6-f18a-4e3e-8b75-0a25df096a4b
-- title:
--   Theorem 1.1 — existence, uniqueness and the dual characterization of the nearest doubly stochastic matrix
-- statement:
--   Let $\hat X\in\mathbb R^{n\times n}$ be given. Consider the nearest doubly stochastic matrix problem
--   $$
--   \min\ \|X-\hat X\|_F^2\quad\text{s.t.}\quad Xe=e,\ X^Te=e,\ X\ge 0 .
--   $$
--   Then:
--
--   1. the optimal solution $X^*$ exists and is unique;
--   2. $X$ solves the problem if and only if
--   $$
--   X=\mathrm{Mat}(\hat x+A^Ty^*)_+,\qquad F(y^*)=A(\hat x+A^Ty^*)_+-b=0
--   $$
--   for some $y^*\in\mathbb R^{2n-1}$.
--
--   The theorem turns the problem into the nonsmooth system $F(y)=0$ of size $2n-1$, which the paper solves by a Newton-type method.
--
--   **Formalization Note** The feasible set is Mathlib's set of doubly stochastic matrices (nonnegative, row and column sums one).
--
--   Differences from the source:
--   - encoding: problem (1.3) in vector form, $\{x\ge 0: Ax=b\}$ with objective $\tfrac12\|x-\hat x\|^2$ → matrices in `doublyStochastic ℝ (Fin (n+1))` with objective $\sum_{a,b}(X_{ab}-\hat X_{ab})^2$; reason: the discarded constraint is implied by the others (p.4) and the factor $\tfrac12$ does not change the minimizer, so the problems have the same solutions (this is problem (1.1))
--   - encoding: size $n\ge1$ → `n + 1`, 0-based indices, $y$ in `Dual n`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Theorem 1.1, p.4 (problems (1.1) p.3, (1.3) p.4, (1.5) p.4)

import Mathlib
import Definitions.Def_NearestDSM_Xmat
import Definitions.Def_NearestDSM_Fres

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Theorem 1.1, p.4. The nearest doubly stochastic matrix `X∗` to `X̂`
(problem (1.1), p.3, equivalently (1.3), p.4) exists and is unique, and `X` is that optimal
solution if and only if `X = Mat(x̂ + Aᵀy∗)₊` with `F(y∗) = 0` for some `y∗ ∈ ℝ^{2n−1}` (1.5).

**Formalization Note.** The paper's size `n ≥ 1` is `n + 1`. The feasible set of (1.3),
`{x ≥ 0, Ax = b}`, is the set of doubly stochastic matrices (the discarded last row-sum
constraint is implied by the others, p.4); it is Mathlib's `doublyStochastic ℝ (Fin (n+1))`
(nonnegative entries, row and column sums one). The objective is the squared Frobenius distance
`‖X − X̂‖²` of (1.1); the factor `1/2` of (1.3) does not change the minimizer. -/
theorem theorem_1_1 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∃! X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, X ∈ doublyStochastic ℝ (Fin (n + 1)) ∧
      ∀ Z ∈ doublyStochastic ℝ (Fin (n + 1)),
        ∑ a, ∑ b, (X a b - Xh a b) ^ 2 ≤ ∑ a, ∑ b, (Z a b - Xh a b) ^ 2) ∧
    ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (X ∈ doublyStochastic ℝ (Fin (n + 1)) ∧ ∀ Z ∈ doublyStochastic ℝ (Fin (n + 1)),
          ∑ a, ∑ b, (X a b - Xh a b) ^ 2 ≤ ∑ a, ∑ b, (Z a b - Xh a b) ^ 2) ↔
        ∃ y : Dual n, X = Xmat Xh y ∧ Fres Xh y = 0 := by sorry

end NearestDSM
