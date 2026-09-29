-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_specialH_sumForm
-- name    : LimitedBFGS.SQN.specialH_sumForm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:26:34.590985+00:00
-- url     : https://prove2.me/theorems/ae6bd702-031e-489a-a9f5-4b1df34a0342
-- title:
--   Property (c), eq. (10), p. 776 — the special matrix $H_{k+1}$ via sum-form updates from $\hat H_{k+1-m} = H_0$
-- statement:
--   Let $H_0$ be symmetric positive definite, $m \ge 1$ the number of stored corrections, and $(s_i), (y_i)$ sequences in $\mathbb{R}^n$ with $y_i^T s_i > 0$ for all $i$. Let $U(s, y, H)$ be the BFGS correction of the sum form (1). For every $k \ge m$ put $\sigma = k + 1 - m$ and define
--
--   $$\hat H_\sigma = H_0, \qquad \hat H_{j+1} = \hat H_j + U(s_j, y_j, \hat H_j), \quad j = \sigma, \sigma+1, \dots, k .$$
--
--   Then the special BFGS matrix (5) satisfies
--
--   $$H_{k+1} = \hat H_{k+1} .$$
--
--   This expresses the limited-storage matrix through the sum form of the BFGS update: $m$ usual BFGS corrections applied to $H_0$, recomputed at every step.
--
--   **Formalization Note** The paper calls the starting index $s$; it is written $\sigma$ here to avoid the clash with the vectors $s_j$. The paper states (10) "for any $k > m$" and gives the case $k = m$ ($H_{m+1} = \hat H_{m+1}$ from $\hat H_1 = H_0$) separately just before; both are covered by $k \ge m$. The sum-form recursion is a left fold over the indices $\sigma, \dots, k$ (`List.range' σ m`).
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 776, Property (c), eqs. (8)–(10)

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix

namespace LimitedBFGS.SQN

/-- Property (c), eq. (10), p. 776: with `m` stored corrections and `y_iᵀs_i > 0` for all `i`,
for every `k ≥ m` the special BFGS matrix `H_{k+1}` is obtained from `Ĥ_start = H₀`,
`start = k + 1 − m`, by the sum-form updates `Ĥ_{j+1} = Ĥ_j + U(s_j, y_j, Ĥ_j)`,
`j = start, …, k`. -/
theorem specialH_sumForm {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef)
    (m : ℕ) (hm : 1 ≤ m) (s y : ℕ → Fin n → ℝ) (hys : ∀ i, 0 < y i ⬝ᵥ s i)
    (k : ℕ) (hk : m ≤ k) :
    specialH H₀ m s y (k + 1) =
      (List.range' (k + 1 - m) m).foldl (fun H j => H + bfgsU H (s j) (y j)) H₀ := by sorry

end LimitedBFGS.SQN
