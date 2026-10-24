-- Prove2me | Theorems.Thm_MatrixAnalytic_MatrixGeometric_matrix_geometric_property
-- name    : MatrixAnalytic.MatrixGeometric.matrix_geometric_property
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:00.017668+00:00
-- url     : https://prove2.me/theorems/c32e63b9-70ac-47bc-8eb7-d220a4485e06
-- title:
--   Theorem 6.2.1 — the matrix-geometric property π_{n+1} = π_n A₀ N, π_n = π₀Rⁿ, with N and R expected numbers of visits
-- statement:
--   Consider a homogeneous quasi-birth-and-death process: an irreducible Markov chain on the states $(n,i)$, $n\ge0$, $i$ in a finite or countably infinite phase set, with block-tridiagonal transition matrix built from $B,A_0,A_1,A_2$ (Eq. (6.1)). Assume it is positive recurrent and let $\pi=(\pi_0,\pi_1,\dots)$ be its stationary probability vector, partitioned by levels. Then there is a nonnegative matrix $N$ indexed by phases such that
--   $$\pi_{n+1}=\pi_nA_0N\qquad\text{for }n\ge0,$$
--   where, for every $n\ge1$, $N_{ij}$ equals the expected number of visits to $(n,j)$, starting from $(n,i)$, before the first visit to any state of $\ell(n-1)$ (in particular this number is finite and independent of $n$). Moreover
--   $$\pi_n=\pi_0R^n\qquad\text{for }n\ge0,$$
--   where $R=A_0N$ is such that, for every $n\ge0$, $R_{ij}$ is the expected number of visits to $(n+1,j)$ before a return to $\ell(0)\cup\cdots\cup\ell(n)$, given that the process starts in $(n,i)$.
--
--   This is the matrix-geometric form of the stationary distribution of a QBD, the matrix analogue of the geometric distribution of a birth-and-death chain, and the base of the whole matrix analytic theory.
--
--   **Formalization Note** $N$ and $R$ are not defined by any equation: the expected numbers of visits are sums over taboo trajectories of products of transition probabilities, valued in $[0,+\infty]$, and the theorem asserts that they equal the entries of the real nonnegative matrices $N$ and $A_0N$. Vector–matrix products and matrix powers are computed in $[0,+\infty]$, so no summability is assumed (the phase set may be infinite). Positive recurrence is the return-time notion at every state; aperiodicity, a temporary standing assumption of §6.2 used only to read $\pi$ as a limit, is omitted.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 131, Theorem 6.2.1, Eq. (6.2)

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

open scoped ENNReal

namespace MatrixAnalytic.MatrixGeometric

/-- Theorem 6.2.1 (p. 131). For a positive recurrent (irreducible) QBD with stationary
distribution `π` there is a nonnegative matrix `N` with `π_{n+1} = π_n A₀ N` for `n ≥ 0`;
`N_{ij}` is the expected number of visits to `(n, j)` from `(n, i)` before the first visit to
`ℓ(n − 1)`, for every `n ≥ 1`; `π_n = π₀ Rⁿ` with `R = A₀N`, and for every `n ≥ 0`, `R_{ij}` is
the expected number of visits to `(n + 1, j)` before a return to `ℓ(0) ∪ ⋯ ∪ ℓ(n)`, starting
from `(n, i)`. Products of nonnegative matrices are computed in `ℝ≥0∞`. -/
theorem matrix_geometric_property {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x)
    (hπ : IsStationaryC (qbdP B A₀ A₁ A₂) π) :
    ∃ N : ι → ι → ℝ, (∀ i j, 0 ≤ N i j) ∧
      (∀ n : ℕ, ∀ j : ι, ENNReal.ofReal (π (n + 1, j)) =
        vecMulE (vecMulE (fun i => ENNReal.ofReal (π (n, i))) (ennMat A₀)) (ennMat N) j) ∧
      (∀ n : ℕ, 1 ≤ n → matN (qbdP B A₀ A₁ A₂) n = ennMat N) ∧
      (∀ n : ℕ, ∀ j : ι, ENNReal.ofReal (π (n, j)) =
        vecMulE (fun i => ENNReal.ofReal (π (0, i)))
          (matPowE (matMulE (ennMat A₀) (ennMat N)) n) j) ∧
      (∀ n : ℕ, matR (qbdP B A₀ A₁ A₂) n = matMulE (ennMat A₀) (ennMat N)) := by sorry

end MatrixAnalytic.MatrixGeometric
