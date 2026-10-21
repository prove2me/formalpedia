-- Prove2me | Theorems.Thm_MatrixAnalytic_FiniteQBD_restricted_process
-- name    : MatrixAnalytic.FiniteQBD.restricted_process
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:57.202541+00:00
-- url     : https://prove2.me/theorems/52dc4856-4216-43d3-aa33-3858f69ff78e
-- title:
--   Lemma 10.1.1 — the process restricted on S_i has transition matrix P_(i), with C_i = A₁ + A₂(I − C_{i−1})⁻¹A₀
-- statement:
--   Let $P$ be the transition matrix (10.2) of an irreducible finite QBD with levels $0, \dots, M$, $M \ge 1$, and a finite phase set, so that $P$ is stochastic. Let $S_i = \bigcup_{i \le n \le M} \ell(n)$ and let $C_0, \dots, C_M$ be defined by
--   $$C_0 = P_{00}, \qquad C_i = A_1 + A_2(I - C_{i-1})^{-1}A_0 \ (1 \le i \le M-1), \qquad C_M = P_{MM} + A_2(I - C_{M-1})^{-1}A_0.$$
--   Then:
--
--   1. For $0 \le i \le M$, the transition matrix of the process restricted on $S_i$ is
--   $$P_{(i)} = \begin{bmatrix} C_i & A_0 & & \\ A_2 & A_1 & \ddots & \\ & \ddots & \ddots & A_0 \\ & & A_2 & P_{MM}\end{bmatrix}$$
--   (and $P_{(M)} = C_M$): for states $x, y \in S_i$, the probability, starting from $x$, that the first visit to $S_i$ after time $0$ is a visit to $y$ equals $(C_i)_{jk}$ if $x = (i, j)$ and $y = (i, k)$, and $P_{xy}$ otherwise.
--   2. For $0 \le i \le M-1$, $I - C_i$ is invertible.
--   3. For $0 \le i \le M-1$, $C_i$ records the probability, starting from the level $i$, of returning to the level $i$ before reaching the level $i+1$: $(C_i)_{jk}$ is the probability, from $(i, j)$, that the first visit to $\ell(i) \cup \ell(i+1)$ after time $0$ is a visit to $(i, k)$.
--   4. For $0 \le i \le M-1$, $(I - C_i)^{-1}A_0$ records the first passage probabilities from $\ell(i)$ to $\ell(i+1)$: its $(j, k)$ entry is the probability, from $(i, j)$, that the first visit to $\ell(i+1)$ is a visit to $(i+1, k)$.
--
--   This is the first phase of the linear level reduction: the levels are removed one at a time from the bottom, and $C_M$ is the transition matrix of the chain watched on the top level only.
--
--   **Formalization Note** "The probability that the first visit to $A$ after time $0$ is a visit to $y$" is the sum over $t \ge 0$ of the taboo first-entrance probabilities `firstEntryStep P A x y t` (trajectory sums of products of one-step probabilities); each statement asserts that this series converges (`HasSum`) to the stated matrix entry. The restricted process's transition matrix is taken in this probabilistic form (the form Theorem 5.3.1 identifies), not by a formula. Irreducibility is the book's standing assumption ("the QBD is finite and irreducible", p. 235). The $C_i$ are defined by the recursion (10.3) with Mathlib's matrix inverse, and invertibility of $I - C_i$ is part of the conclusion. $M \ge 1$ and a nonempty phase set are assumed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 222–223, Lemma 10.1.1

import Mathlib
import Definitions.Def_MatrixAnalytic_FiniteQBD_Chain
import Definitions.Def_MatrixAnalytic_FiniteQBD_QBD

namespace MatrixAnalytic.FiniteQBD

/-- Latouche & Ramaswami, Lemma 10.1.1 (pp. 222–223). Let `P` be the transition matrix (10.2) of
an irreducible finite QBD with levels `0, …, M` (`M ≥ 1`) and finitely many phases, and let
`C₀ = P₀₀`, `C_i = A₁ + A₂(I − C_{i−1})⁻¹A₀` (`1 ≤ i ≤ M − 1`), `C_M = P_{MM} + A₂(I − C_{M−1})⁻¹A₀`.
1. For `0 ≤ i ≤ M`, the transition matrix of the process restricted on `S_i = ⋃_{i ≤ n ≤ M} ℓ(n)`
   (entry `(x, y)`: the probability, from `x`, that the first visit to `S_i` after time `0` is a
   visit to `y`) is `P_{(i)}`: it equals `C_i` on `ℓ(i) × ℓ(i)` and agrees with `P` elsewhere.
2. For `0 ≤ i ≤ M − 1`, `I − C_i` is invertible.
3. For `0 ≤ i ≤ M − 1`, `C_i` records the probability, starting from `ℓ(i)`, of returning to
   `ℓ(i)` before reaching `ℓ(i+1)`.
4. For `0 ≤ i ≤ M − 1`, `(I − C_i)⁻¹A₀` records the first passage probabilities from `ℓ(i)` to
   `ℓ(i+1)`. -/
theorem restricted_process {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (P : Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ)
    (hPdef : P = qbdMatrix M P00 A0 A1 A2 PMM)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) :
    -- 1. the restricted process on `S_i` has transition matrix `P_{(i)}`
    (∀ i : ℕ, i ≤ M → ∀ x y : Fin (M + 1) × ι,
      x ∈ levelsFrom M ι i → y ∈ levelsFrom M ι i →
      HasSum (fun t => firstEntryStep P (levelsFrom M ι i) x y t)
        (if (x.1 : ℕ) = i ∧ (y.1 : ℕ) = i then Cmat M P00 A0 A1 A2 PMM i x.2 y.2 else P x y)) ∧
    -- 2. `I − C_i` is invertible
    (∀ i : ℕ, i < M → IsUnit (1 - Cmat M P00 A0 A1 A2 PMM i)) ∧
    -- 3. `C_i`: return to `ℓ(i)` before reaching `ℓ(i+1)`
    (∀ i : ℕ, i < M → ∀ x y : Fin (M + 1) × ι, (x.1 : ℕ) = i → (y.1 : ℕ) = i →
      HasSum (fun t => firstEntryStep P (level M ι i ∪ level M ι (i + 1)) x y t)
        (Cmat M P00 A0 A1 A2 PMM i x.2 y.2)) ∧
    -- 4. `(I − C_i)⁻¹A₀`: first passage from `ℓ(i)` to `ℓ(i+1)`
    (∀ i : ℕ, i < M → ∀ x y : Fin (M + 1) × ι, (x.1 : ℕ) = i → (y.1 : ℕ) = i + 1 →
      HasSum (fun t => firstEntryStep P (level M ι (i + 1)) x y t)
        (((1 - Cmat M P00 A0 A1 A2 PMM i)⁻¹ * A0) x.2 y.2)) := by sorry

end MatrixAnalytic.FiniteQBD
