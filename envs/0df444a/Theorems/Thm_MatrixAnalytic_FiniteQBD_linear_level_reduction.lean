-- Prove2me | Theorems.Thm_MatrixAnalytic_FiniteQBD_linear_level_reduction
-- name    : MatrixAnalytic.FiniteQBD.linear_level_reduction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:05.064611+00:00
-- url     : https://prove2.me/theorems/87fe6912-9adf-44ed-9e5c-4b34fc9784f5
-- title:
--   Theorem 10.1.2 — π_M = π_M C_M, π_i = π_{i+1}A₂(I − C_i)⁻¹, Σπ_i1 = 1 determine π
-- statement:
--   Let $P$ be the transition matrix (10.2) of an irreducible finite QBD with levels $0, \dots, M$, $M \ge 1$, and a finite phase set, let $\pi = (\pi_0, \pi_1, \dots, \pi_M)$ be its stationary probability vector, and let $C_0, \dots, C_M$ be the matrices (10.3) of Lemma 10.1.1. Then $I - C_i$ is invertible for $0 \le i \le M-1$, and the stationary vector is determined by the equations
--   $$\pi_M = \pi_M C_M, \qquad \pi_i = \pi_{i+1}A_2(I - C_i)^{-1} \ (0 \le i \le M-1), \qquad \sum_{0 \le i \le M}\pi_i\mathbf 1 = 1:$$
--   $\pi$ satisfies them, and every real row vector that satisfies them is equal to $\pi$.
--
--   Together with Lemma 10.1.1 this is the linear level reduction algorithm (Figure 10.1): compute $C_0, \dots, C_M$ upwards, solve for the stationary vector of $C_M$, and recover the lower levels by backward substitution.
--
--   **Formalization Note** "Determined by" is formalized as both directions: $\pi$ satisfies (10.4)–(10.6), and any real vector satisfying them is $\pi$. The vector $\pi$ is a hypothesis (nonnegative, sums to one, $\pi P = \pi$); its existence for a finite irreducible chain is standard. Irreducibility is the book's standing assumption; $M \ge 1$ and a nonempty phase set are assumed. Invertibility of $I - C_i$ is concluded, not assumed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 223, Theorem 10.1.2

import Mathlib
import Definitions.Def_MatrixAnalytic_FiniteQBD_Chain
import Definitions.Def_MatrixAnalytic_FiniteQBD_QBD

namespace MatrixAnalytic.FiniteQBD

open Matrix

/-- Latouche & Ramaswami, Theorem 10.1.2 (p. 223). Let `P` be the transition matrix (10.2) of an
irreducible finite QBD with levels `0, …, M` (`M ≥ 1`) and finitely many phases, with stationary
probability vector `π = (π₀, π₁, …, π_M)`, and let `C_i` be the matrices (10.3) of Lemma 10.1.1.
Then `I − C_i` is invertible for `0 ≤ i ≤ M − 1`, and `π` is determined by the equations
`π_M = π_M C_M` (10.4), `π_i = π_{i+1} A₂ (I − C_i)⁻¹` for `0 ≤ i ≤ M − 1` (10.5) and
`∑_{0 ≤ i ≤ M} π_i 1 = 1` (10.6): `π` satisfies them, and any real row vector satisfying them
is `π`. -/
theorem linear_level_reduction {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (P : Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ)
    (hPdef : P = qbdMatrix M P00 A0 A1 A2 PMM)
    (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (π : Fin (M + 1) × ι → ℝ) (hπ : IsStationaryC P π) :
    (∀ i : ℕ, i < M → IsUnit (1 - Cmat M P00 A0 A1 A2 PMM i)) ∧
    -- `π` satisfies (10.4)–(10.6)
    (block π M = block π M ᵥ* Cmat M P00 A0 A1 A2 PMM M) ∧
    (∀ i : ℕ, i < M →
      block π i = block π (i + 1) ᵥ* (A2 * (1 - Cmat M P00 A0 A1 A2 PMM i)⁻¹)) ∧
    (∑ i ∈ Finset.range (M + 1), ∑ j : ι, block π i j = 1) ∧
    -- and (10.4)–(10.6) determine `π`
    (∀ p : Fin (M + 1) × ι → ℝ,
      block p M = block p M ᵥ* Cmat M P00 A0 A1 A2 PMM M →
      (∀ i : ℕ, i < M →
        block p i = block p (i + 1) ᵥ* (A2 * (1 - Cmat M P00 A0 A1 A2 PMM i)⁻¹)) →
      ∑ i ∈ Finset.range (M + 1), ∑ j : ι, block p i j = 1 →
      p = π) := by sorry

end MatrixAnalytic.FiniteQBD
