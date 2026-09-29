-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_bfgsV_mulVec_of_conjugate
-- name    : LimitedBFGS.SQN.bfgsV_mulVec_of_conjugate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:25:30.955975+00:00
-- url     : https://prove2.me/theorems/d69334b6-7373-43eb-8317-c62803585715
-- title:
--   Eq. (7), p. 776 — $v_i y_i = 0$ and $v_i y_j = y_j$ for $i > j$ along conjugate steps
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ be a strictly convex quadratic ($A$ symmetric positive definite), and let $(s_i)_{i \ge 0}$, $(y_i)_{i\ge 0}$ be sequences in $\mathbb{R}^n$ with $y_j = A s_j$ for all $j$ (the gradient differences of $f$), and let $N \ge 0$. Suppose the steps $s_0, \dots, s_{N-1}$ are conjugate,
--
--   $$s_i^T A s_j = 0 \quad (i \neq j,\ i, j < N),$$
--
--   and $y_i^T s_i > 0$ for $i < N$. Let $\rho_i = 1/y_i^T s_i$ and $v_i = I - \rho_i y_i s_i^T$. Then
--
--   $$v_i y_i = 0 \ \text{ for } i < N, \qquad v_i y_j = y_j \ \text{ for } j < i < N .$$
--
--   These two identities are the computation behind Property (b): they make the special BFGS matrices satisfy the quasi-Newton equation in the $m$ most recent directions.
--
--   **Formalization Note** The paper states the first identity for $i = k, k-1, \dots, k-m+1$, the indices used in (6); it holds for every conjugate step and is stated so. The conjugate steps are indexed up to a finite horizon $N$: infinitely many nonzero, mutually $A$-conjugate vectors do not exist in $\mathbb{R}^n$, so requiring conjugacy and $y_i^T s_i > 0$ for all $i \in \mathbb{N}$ would make the hypotheses unsatisfiable. Vectors are `Fin n → ℝ`.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), pp. 775–776, Property (b), eq. (7)

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_bfgsStep

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (7), p. 776: for a strictly convex quadratic with Hessian `A`, pairs `y_j = A s_j`,
steps `s_0, …, s_{N−1}` that are conjugate (`s_iᵀ A s_j = 0`, `i ≠ j`) with `y_iᵀs_i > 0`, the
matrices `v_i = I − ρ_i y_i s_iᵀ` satisfy `v_i y_i = 0` and `v_i y_j = y_j` for `j < i < N`. -/
theorem bfgsV_mulVec_of_conjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (s y : ℕ → Fin n → ℝ) (N : ℕ) (hy : ∀ j, y j = A *ᵥ s j)
    (hconj : ∀ i j, i < N → j < N → i ≠ j → s i ⬝ᵥ (A *ᵥ s j) = 0)
    (hys : ∀ i, i < N → 0 < y i ⬝ᵥ s i) :
    (∀ i, i < N → bfgsV (s i) (y i) *ᵥ y i = 0) ∧
      (∀ i j, j < i → i < N → bfgsV (s i) (y i) *ᵥ y j = y j) := by sorry

end LimitedBFGS.SQN
