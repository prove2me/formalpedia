-- Prove2me | Theorems.Thm_MatrixAnalytic_FiniteQBD_matrix_product_form
-- name    : MatrixAnalytic.FiniteQBD.matrix_product_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:03.035701+00:00
-- url     : https://prove2.me/theorems/0fdc0580-ea3b-468f-b271-7dcdf8bf4193
-- title:
--   Theorem 10.1.3 — π₀ = π₀U^{(0)}, π_i = π_{i−1}R^{(i)} with R^{(i)} = A₀(I − U^{(i)})⁻¹, U^{(i)} built backwards from U^{(M)} = P_MM
-- statement:
--   Let $P$ be the transition matrix (10.2) of an irreducible finite QBD with levels $0, \dots, M$, $M \ge 1$, and a finite phase set, with stationary probability vector $\pi = (\pi_0, \dots, \pi_M)$. Define, backwards from the top level,
--   $$U^{(M)} = P_{MM}, \qquad U^{(i)} = A_1 + A_0(I - U^{(i+1)})^{-1}A_2 \ (1 \le i \le M-1), \qquad U^{(0)} = P_{00} + A_0(I - U^{(1)})^{-1}A_2,$$
--   and $R^{(i)} = A_0(I - U^{(i)})^{-1}$ for $1 \le i \le M$. Then:
--
--   1. $I - U^{(i)}$ is invertible for $1 \le i \le M$.
--   2. The stationary vector is given by
--   $$\pi_0 = \pi_0U^{(0)}, \qquad \pi_i = \pi_{i-1}R^{(i)} \quad (1 \le i \le M),$$
--   and these equations determine it up to a multiplicative constant: every real row vector satisfying them is a scalar multiple of $\pi$.
--   3. For $1 \le i \le M$, $U^{(i)}$ records the transition probability from $\ell(i)$ to $\ell(i)$ before a visit to $\ell(i-1)$: $(U^{(i)})_{jk}$ is the probability, from $(i, j)$, that the first visit to $\ell(i) \cup \ell(i-1)$ after time $0$ is a visit to $(i, k)$.
--   4. For $1 \le i \le M$, $(I - U^{(i)})^{-1}A_2$ records the first passage probabilities from $\ell(i)$ to $\ell(i-1)$: its $(j, k)$ entry is the probability, from $(i, j)$, that the first visit to $\ell(i-1)$ is a visit to $(i-1, k)$.
--
--   This is the matrix-product form of the stationary vector of a finite QBD, the finite counterpart of the matrix-geometric form $\pi_n = \pi_{n-1}R$, $R = A_0(I - U)^{-1}$ of the infinite QBD: the matrices $U^{(i)}$ depend on the level because of the upper boundary.
--
--   **Formalization Note** The probabilities in items 3 and 4 are sums over $t \ge 0$ of taboo first-entrance probabilities `firstEntryStep` (trajectory sums of products of one-step probabilities), asserted to converge (`HasSum`) to the stated entries. The $U^{(i)}$ are defined by the recursion (10.8)–(10.9) with Mathlib's matrix inverse; invertibility of $I - U^{(i)}$ is part of the conclusion. "The stationary vector is given by" is formalized as: $\pi$ satisfies (10.7), and (10.7) determines it up to a constant (the book states no normalization here). The vector $\pi$ is a hypothesis (nonnegative, sums to one, $\pi P = \pi$). Irreducibility is the book's standing assumption; $M \ge 1$ and a nonempty phase set are assumed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 224–225, Theorem 10.1.3

import Mathlib
import Definitions.Def_MatrixAnalytic_FiniteQBD_Chain
import Definitions.Def_MatrixAnalytic_FiniteQBD_QBD

namespace MatrixAnalytic.FiniteQBD

open Matrix

/-- Latouche & Ramaswami, Theorem 10.1.3 (pp. 224–225). Let `P` be the transition matrix (10.2) of
an irreducible finite QBD with levels `0, …, M` (`M ≥ 1`) and finitely many phases, with stationary
probability vector `π = (π₀, …, π_M)`. Let `U^{(M)} = P_{MM}`,
`U^{(i)} = A₁ + A₀(I − U^{(i+1)})⁻¹A₂` for `1 ≤ i ≤ M − 1`, `U^{(0)} = P₀₀ + A₀(I − U^{(1)})⁻¹A₂`,
and `R^{(i)} = A₀(I − U^{(i)})⁻¹` for `1 ≤ i ≤ M`.
1. `I − U^{(i)}` is invertible for `1 ≤ i ≤ M`.
2. The stationary vector is given by `π₀ = π₀U^{(0)}` and `π_i = π_{i−1}R^{(i)}` for
   `1 ≤ i ≤ M` (10.7); these equations determine it up to a multiplicative constant: every real
   row vector satisfying them is a scalar multiple of `π`.
3. For `1 ≤ i ≤ M`, `U^{(i)}` records the transition probability from `ℓ(i)` to `ℓ(i)` before a
   visit to `ℓ(i−1)` (the first visit to `ℓ(i) ∪ ℓ(i−1)` after time `0` is a visit to `ℓ(i)`).
4. For `1 ≤ i ≤ M`, `(I − U^{(i)})⁻¹A₂` records the first passage probabilities from `ℓ(i)` to
   `ℓ(i−1)`. -/
theorem matrix_product_form {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (P : Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ)
    (hPdef : P = qbdMatrix M P00 A0 A1 A2 PMM)
    (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (π : Fin (M + 1) × ι → ℝ) (hπ : IsStationaryC P π) :
    -- 1. the inverses in (10.8)–(10.9) exist
    (∀ i : ℕ, 1 ≤ i → i ≤ M → IsUnit (1 - Umat M P00 A0 A1 A2 PMM i)) ∧
    -- 2. (10.7)
    (block π 0 = block π 0 ᵥ* Umat M P00 A0 A1 A2 PMM 0) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ M → block π i = block π (i - 1) ᵥ* Rmat M P00 A0 A1 A2 PMM i) ∧
    -- (10.7) determines `π` up to a multiplicative constant
    (∀ p : Fin (M + 1) × ι → ℝ,
      block p 0 = block p 0 ᵥ* Umat M P00 A0 A1 A2 PMM 0 →
      (∀ i : ℕ, 1 ≤ i → i ≤ M → block p i = block p (i - 1) ᵥ* Rmat M P00 A0 A1 A2 PMM i) →
      ∃ c : ℝ, p = c • π) ∧
    -- 3. `U^{(i)}`: from `ℓ(i)` back to `ℓ(i)` before a visit to `ℓ(i−1)`
    (∀ i : ℕ, 1 ≤ i → i ≤ M → ∀ x y : Fin (M + 1) × ι, (x.1 : ℕ) = i → (y.1 : ℕ) = i →
      HasSum (fun t => firstEntryStep P (level M ι i ∪ level M ι (i - 1)) x y t)
        (Umat M P00 A0 A1 A2 PMM i x.2 y.2)) ∧
    -- 4. `(I − U^{(i)})⁻¹A₂`: first passage from `ℓ(i)` to `ℓ(i−1)`
    (∀ i : ℕ, 1 ≤ i → i ≤ M → ∀ x y : Fin (M + 1) × ι, (x.1 : ℕ) = i → (y.1 : ℕ) = i - 1 →
      HasSum (fun t => firstEntryStep P (level M ι (i - 1)) x y t)
        (((1 - Umat M P00 A0 A1 A2 PMM i)⁻¹ * A2) x.2 y.2)) := by sorry

end MatrixAnalytic.FiniteQBD
