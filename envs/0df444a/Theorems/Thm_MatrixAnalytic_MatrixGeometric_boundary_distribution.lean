-- Prove2me | Theorems.Thm_MatrixAnalytic_MatrixGeometric_boundary_distribution
-- name    : MatrixAnalytic.MatrixGeometric.boundary_distribution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:10.755055+00:00
-- url     : https://prove2.me/theorems/4584dca9-ecc7-41fe-bae3-3e763186ef95
-- title:
--   Lemma 6.3.1 — π₀ is the unique solution of π₀(B + A₀G) = π₀, π₀(I − R)⁻¹1 = 1 (finitely many phases)
-- statement:
--   Consider an irreducible, positive recurrent homogeneous QBD with blocks $B,A_0,A_1,A_2$, a finite set of phases, and stationary distribution $\pi=(\pi_0,\pi_1,\dots)$. Let $G$ be the matrix (6.6) at level $1$, $G_{ij}$ the probability, starting from $(1,i)$, of reaching $\ell(0)$ and doing so first at $(0,j)$, and let $R$ be the matrix of Theorem 6.2.1 at level $0$, $R_{ij}$ the expected number of visits to $(1,j)$ from $(0,i)$ before a return to $\ell(0)$. Then the entries of $G$ and $R$ are finite, $I-R$ is invertible, and the stationary vector $\pi_0$ of the boundary level $\ell(0)$ is the unique (real) solution of the system
--   $$\pi_0(B+A_0G)=\pi_0,\qquad \pi_0(I-R)^{-1}\mathbf 1=1.$$
--   Moreover $B+A_0G=B+RA_2$, so the first equation may also be written $\pi_0(B+RA_2)=\pi_0$.
--
--   Together with $\pi_n=\pi_0R^n$ this determines the whole stationary distribution from $R$ (or $G$).
--
--   **Formalization Note** The statement is made for a finite phase set, where $(I-R)^{-1}$ is a matrix inverse and "every vector" is a vector of $\mathbb R^m$; invertibility of $I-R$ is part of the conclusion, not an assumption. Uniqueness is among all real vectors, not only probability vectors, as on the page. $G$ and $R$ are defined probabilistically, asserted finite, and read as real matrices. Aperiodicity is not used and is omitted.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 139, Lemma 6.3.1

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

open scoped ENNReal

namespace MatrixAnalytic.MatrixGeometric

/-- Lemma 6.3.1 (p. 139), for a finite number of phases. Let `G` be the first-passage matrix
(6.6) from `ℓ(1)` to `ℓ(0)` and `R` the expected-visits matrix of Theorem 6.2.1 from `ℓ(0)` to
`ℓ(1)`, read as real matrices (their entries are finite and `I − R` is invertible). The
stationary subvector `π₀` of `ℓ(0)` satisfies `π₀(B + A₀G) = π₀` and `π₀(I − R)⁻¹1 = 1`, it is
the only real vector satisfying both, and `B + A₀G = B + RA₂`. -/
theorem boundary_distribution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x)
    (hπ : IsStationaryC (qbdP B A₀ A₁ A₂) π) :
    let G : Matrix ι ι ℝ := Matrix.of fun i j => (matG (qbdP B A₀ A₁ A₂) 1 i j).toReal
    let R : Matrix ι ι ℝ := Matrix.of fun i j => (matR (qbdP B A₀ A₁ A₂) 0 i j).toReal
    let π₀ : ι → ℝ := fun i => π (0, i)
    (∀ i j, matG (qbdP B A₀ A₁ A₂) 1 i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤) ∧
      IsUnit (1 - R) ∧
      Matrix.vecMul π₀ (Matrix.of B + Matrix.of A₀ * G) = π₀ ∧
      dotProduct (Matrix.vecMul π₀ (1 - R)⁻¹) (fun _ => 1) = 1 ∧
      (∀ x : ι → ℝ, Matrix.vecMul x (Matrix.of B + Matrix.of A₀ * G) = x →
        dotProduct (Matrix.vecMul x (1 - R)⁻¹) (fun _ => 1) = 1 → x = π₀) ∧
      Matrix.of B + Matrix.of A₀ * G = Matrix.of B + R * Matrix.of A₂ := by sorry

end MatrixAnalytic.MatrixGeometric
