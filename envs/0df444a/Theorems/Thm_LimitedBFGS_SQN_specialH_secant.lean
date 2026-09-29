-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_specialH_secant
-- name    : LimitedBFGS.SQN.specialH_secant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:25:59.048007+00:00
-- url     : https://prove2.me/theorems/0f8791da-b2ed-4ecc-ad47-0fc21f47b4d0
-- title:
--   Property (b), eq. (6), p. 776 — quasi-Newton equation $H_k y_j = s_j$ in the past $m$ directions
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ be a strictly convex quadratic ($A$ symmetric positive definite), $H_0$ symmetric positive definite, and $m \ge 1$ the number of stored corrections. Let $(s_i), (y_i)$ be sequences in $\mathbb{R}^n$ with $y_j = A s_j$, let $k > m$, and suppose the steps $s_0, \dots, s_{k-1}$ are conjugate, $s_i^T A s_j = 0$ for $i \ne j$, with $y_i^T s_i > 0$ for $i < k$. Let $H_k$ be the special BFGS matrix (4)–(5) built from these pairs. Then
--
--   $$H_k y_j = s_j, \qquad j = k-1, \dots, k-m .$$
--
--   That is, although $H_k$ keeps only the last $m$ corrections, it satisfies the secant (quasi-Newton) equation exactly on the $m$ most recent directions.
--
--   **Formalization Note** $H_k$ is `specialH H₀ m s y k`, i.e. $H_0$ updated by the pairs $j = k - m, \dots, k-1$ when $k > m$. The range "$j = k-1, \dots, k-m$" is encoded as $k - m \le j < k$. Conjugacy and $y_i^T s_i > 0$ are assumed for the steps $s_0, \dots, s_{k-1}$ that precede $H_k$, not for all $i \in \mathbb{N}$: infinitely many nonzero, mutually $A$-conjugate vectors do not exist in $\mathbb{R}^n$, so the latter would make the hypotheses unsatisfiable.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), pp. 775–776, Property (b), eq. (6)

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix

namespace LimitedBFGS.SQN

/-- Property (b), eq. (6), pp. 775–776: for a strictly convex quadratic with Hessian `A`, pairs
`y_j = A s_j`, conjugate steps `s_0, …, s_{k−1}` with `y_iᵀs_i > 0`, the special BFGS matrix `H_k`
satisfies the quasi-Newton equation in the past `m` directions: `H_k y_j = s_j` for
`j = k − 1, …, k − m`, whenever `k > m`. -/
theorem specialH_secant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (s y : ℕ → Fin n → ℝ) (k : ℕ) (hk : m < k) (hy : ∀ j, y j = A *ᵥ s j)
    (hconj : ∀ i j, i < k → j < k → i ≠ j → s i ⬝ᵥ (A *ᵥ s j) = 0)
    (hys : ∀ i, i < k → 0 < y i ⬝ᵥ s i) (j : ℕ) (hj₁ : k - m ≤ j) (hj₂ : j < k) :
    specialH H₀ m s y k *ᵥ y j = s j := by sorry

end LimitedBFGS.SQN
