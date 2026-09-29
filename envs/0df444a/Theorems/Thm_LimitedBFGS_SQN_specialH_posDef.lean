-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_specialH_posDef
-- name    : LimitedBFGS.SQN.specialH_posDef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:25:01.062985+00:00
-- url     : https://prove2.me/theorems/738eceda-d1fe-4951-ab06-fc3b9dfddecf
-- title:
--   Property (a), p. 775 — the special BFGS matrices are positive definite
-- statement:
--   Let $H_0$ be a symmetric positive definite $n \times n$ matrix, let $m \ge 0$ be the number of stored corrections, and let $(s_i, y_i)_{i \ge 0}$ be any sequences of vectors in $\mathbb{R}^n$ with
--
--   $$y_i^T s_i > 0 \quad \text{for all } i .$$
--
--   Then every special BFGS matrix $H_K$ of (4)–(5) (that is, $H_0$ updated by the BFGS product form with the pairs $(s_j,y_j)$, $j = K - \min(K,m), \dots, K-1$) is symmetric positive definite:
--
--   $$H_K \succ 0 \qquad \text{for every } K \ge 0 .$$
--
--   Positive definiteness is what makes $d = -H_K g$ a descent direction; it is the basic well-posedness property of the limited-storage method.
--
--   **Formalization Note** Positive definiteness is Mathlib's `Matrix.PosDef`, which over $\mathbb{R}$ includes symmetry. The hypothesis $y_i^T s_i > 0$ is the paper's standing assumption (p. 774), stated for arbitrary sequences.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 775, Property (a)

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix

namespace LimitedBFGS.SQN

/-- Property (a), p. 775: if `H₀` is positive definite and `y_iᵀs_i > 0` for all `i`, every
special BFGS matrix (4)–(5) is positive definite. -/
theorem specialH_posDef {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ)
    (s y : ℕ → Fin n → ℝ) (hys : ∀ i, 0 < y i ⬝ᵥ s i) (K : ℕ) :
    (specialH H₀ m s y K).PosDef := by sorry

end LimitedBFGS.SQN
