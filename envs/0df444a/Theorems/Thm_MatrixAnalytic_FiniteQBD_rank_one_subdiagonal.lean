-- Prove2me | Theorems.Thm_MatrixAnalytic_FiniteQBD_rank_one_subdiagonal
-- name    : MatrixAnalytic.FiniteQBD.rank_one_subdiagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:59.480986+00:00
-- url     : https://prove2.me/theorems/ddb640e0-fadd-4734-a599-d850f6a839b0
-- title:
--   Theorem 10.4.1 — if A₂ (or A₀) = c·r has rank 1, then π_i = π₀Rⁱ with R = A₀(I − A₁ − A₀1·r)⁻¹ (resp. π_{M−i} = π_M R̂ⁱ)
-- statement:
--   Let $P$ be the transition matrix (10.2) of an irreducible finite QBD with levels $0, \dots, M$, $M \ge 1$, and a finite phase set, with stationary probability vector $\pi = (\pi_0, \dots, \pi_M)$; $\mathbf 1$ is the column vector of ones.
--
--   1. If $A_2$ is of rank 1 and $A_2 = \boldsymbol c\cdot\boldsymbol r$ (a column vector times a row vector) with $\boldsymbol r\mathbf 1 = 1$, let
--   $$R = A_0(I - A_1 - A_0\mathbf 1\cdot\boldsymbol r)^{-1}, \qquad R_M = A_0(I - P_{MM})^{-1}.$$
--   Then $I - P_{MM}$ is invertible, $I - A_1 - A_0\mathbf 1\cdot\boldsymbol r$ is invertible when $M \ge 2$, and the stationary distribution is given by
--   $$\pi_i = \pi_0R^i \ (1 \le i \le M-1), \qquad \pi_M = \pi_0R^{M-1}R_M, \qquad \pi\mathbf 1 = 1, \qquad \pi_0(I - P_{00} - A_0\mathbf 1\cdot\boldsymbol r) = \mathbf 0:$$
--   a real row vector satisfies these four conditions if and only if it is $\pi$.
--   2. If $A_0$ is of rank 1 and $A_0 = \boldsymbol c\cdot\boldsymbol r$ with $\boldsymbol r\mathbf 1 = 1$, let
--   $$\hat R = A_2(I - A_1 - A_2\mathbf 1\cdot\boldsymbol r)^{-1}, \qquad \hat R_0 = A_2(I - P_{00})^{-1}.$$
--   Then $I - P_{00}$ is invertible, $I - A_1 - A_2\mathbf 1\cdot\boldsymbol r$ is invertible when $M \ge 2$, and a real row vector satisfies
--   $$\pi_{M-i} = \pi_M\hat R^i \ (1 \le i \le M-1), \qquad \pi_0 = \pi_M\hat R^{M-1}\hat R_0, \qquad \pi\mathbf 1 = 1, \qquad \pi_M(I - P_{MM} - A_2\mathbf 1\cdot\boldsymbol r) = \mathbf 0$$
--   if and only if it is $\pi$.
--
--   This covers the M/PH/1/K and PH/M/1/K queues: the stationary vector is obtained from one $m \times m$ system whatever the number of levels.
--
--   **Formalization Note** "The stationary distribution is given by" is formalized as: the listed equations hold for $\pi$ and determine it (an "if and only if" over real row vectors). The invertibility of the matrices inverted in $R, R_M$ (resp. $\hat R, \hat R_0$) is part of the conclusion; when $M = 1$ the matrix $R$ (resp. $\hat R$) enters only as $R^0 = I$, and its inverse is then not claimed (with $M = 1$ the block $A_1$ does not occur in (10.2), so $I - A_1 - A_0\mathbf 1\cdot\boldsymbol r$ may be singular). The $\hat R$ here is the one of this theorem, not the rate matrix of the level-reversed process of §10.3. Irreducibility is the book's standing assumption ("the QBD is finite and irreducible", p. 235); $M \ge 1$ and a nonempty phase set are assumed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 236, Theorem 10.4.1

import Mathlib
import Definitions.Def_MatrixAnalytic_FiniteQBD_Chain
import Definitions.Def_MatrixAnalytic_FiniteQBD_QBD

namespace MatrixAnalytic.FiniteQBD

open Matrix

/-- Latouche & Ramaswami, Theorem 10.4.1 (p. 236). Let `P` be the transition matrix (10.2) of an
irreducible finite QBD with levels `0, …, M` (`M ≥ 1`) and finitely many phases, with stationary
probability vector `π = (π₀, …, π_M)`; `1` is the column vector of ones.

First statement. If `A₂` is of rank 1 and `A₂ = c·r` (column `c`, row `r`) with `r1 = 1`, put
`R = A₀(I − A₁ − A₀1·r)⁻¹` and `R_M = A₀(I − P_{MM})⁻¹`. Then `I − P_{MM}` is invertible, so is
`I − A₁ − A₀1·r` when `M ≥ 2` (when `M = 1` the matrix `R` enters only as `R⁰ = I`), and the
stationary distribution is given by `π_i = π₀Rⁱ` (`1 ≤ i ≤ M − 1`), `π_M = π₀R^{M−1}R_M`,
`π1 = 1` and `π₀(I − P₀₀ − A₀1·r) = 0` (10.22): `π` satisfies these equations and is the only
real vector that does.

Second statement. If `A₀` is of rank 1 and `A₀ = c·r` with `r1 = 1`, put
`R̂ = A₂(I − A₁ − A₂1·r)⁻¹` and `R̂₀ = A₂(I − P₀₀)⁻¹` (not the `R̂` of §10.3). Then `I − P₀₀` is
invertible, so is `I − A₁ − A₂1·r` when `M ≥ 2`, and the stationary distribution is given by
`π_{M−i} = π_M R̂ⁱ` (`1 ≤ i ≤ M − 1`), `π₀ = π_M R̂^{M−1}R̂₀`, `π1 = 1` and
`π_M(I − P_{MM} − A₂1·r) = 0` (10.23), and `π` is the only real vector satisfying these. -/
theorem rank_one_subdiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (P : Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ)
    (hPdef : P = qbdMatrix M P00 A0 A1 A2 PMM)
    (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (π : Fin (M + 1) × ι → ℝ) (hπ : IsStationaryC P π) :
    -- first statement: `A₂ = c·r` of rank 1, `r1 = 1`
    (∀ c r : ι → ℝ, A2 = vecMulVec c r → A2.rank = 1 → r ⬝ᵥ (fun _ => (1 : ℝ)) = 1 →
      IsUnit (1 - PMM) ∧
      (2 ≤ M → IsUnit (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)) ∧
      ∀ p : Fin (M + 1) × ι → ℝ,
        ((∀ i : ℕ, 1 ≤ i → i ≤ M - 1 →
            block p i =
              block p 0 ᵥ* (A0 * (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ i) ∧
          block p M =
            block p 0 ᵥ* ((A0 * (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ (M - 1) *
              (A0 * (1 - PMM)⁻¹)) ∧
          ∑ x, p x = 1 ∧
          block p 0 ᵥ* (1 - P00 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r) = 0) ↔ p = π) ∧
    -- second statement: `A₀ = c·r` of rank 1, `r1 = 1`
    (∀ c r : ι → ℝ, A0 = vecMulVec c r → A0.rank = 1 → r ⬝ᵥ (fun _ => (1 : ℝ)) = 1 →
      IsUnit (1 - P00) ∧
      (2 ≤ M → IsUnit (1 - A1 - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r)) ∧
      ∀ p : Fin (M + 1) × ι → ℝ,
        ((∀ i : ℕ, 1 ≤ i → i ≤ M - 1 →
            block p (M - i) =
              block p M ᵥ* (A2 * (1 - A1 - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ i) ∧
          block p 0 =
            block p M ᵥ* ((A2 * (1 - A1 - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ (M - 1) *
              (A2 * (1 - P00)⁻¹)) ∧
          ∑ x, p x = 1 ∧
          block p M ᵥ* (1 - PMM - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r) = 0) ↔ p = π) := by sorry

end MatrixAnalytic.FiniteQBD
