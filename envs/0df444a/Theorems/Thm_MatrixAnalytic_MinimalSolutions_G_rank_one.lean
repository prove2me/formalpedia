-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_G_rank_one
-- name    : MatrixAnalytic.MinimalSolutions.G_rank_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:40.459066+00:00
-- url     : https://prove2.me/theorems/979cafca-591b-4ab8-a194-1ab51fbacc34
-- title:
--   Theorem 8.5.1 — if A₂ = c·r has rank one, then G = 1·r
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1), with a countable (finite or infinite) set of phases, and assume that the QBD is recurrent and that
--
--   $$A_2 = \boldsymbol c\cdot\boldsymbol r,$$
--
--   where $\boldsymbol c$ is a column vector and $\boldsymbol r$ is a row vector normalized by $\boldsymbol r\mathbf 1 = 1$. Then the first-passage matrix $G$ (8.3) is
--
--   $$G = \mathbf 1\cdot\boldsymbol r,\qquad\text{i.e. } G_{ij} = r_j \text{ for all phases } i, j.$$
--
--   This covers, for instance, the M/PH/1 queue, where the phase at the end of a downward move does not depend on the phase before it.
--
--   **Formalization Note** The vectors $\boldsymbol c$ and $\boldsymbol r$ are arbitrary real vectors with $(A_2)_{ij} = c_ir_j$ and $\sum_j r_j = 1$ (the sum converging). $G$ is the probabilistic matrix (8.3), with entries in $[0,\infty]$, and the conclusion compares it with $r_j$ read in $[0,\infty]$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 197, Theorem 8.5.1

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Theorem 8.5.1 (p. 197). For an irreducible recurrent QBD (8.1) whose block `A₂ = c · r` is the
product of a column vector `c` and a row vector `r` normalized by `r1 = 1`, the first-passage
matrix `G` (8.3) is `G = 1 · r`, i.e. `G_{ij} = r_j` for all phases `i, j`. -/
theorem G_rank_one {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x)
    (c r : ι → ℝ) (hA₂ : ∀ i j, A₂ i j = c i * r j) (hr : HasSum r 1) :
    ∀ i j, matG (qbdP B A₀ A₁ A₂) i j = ENNReal.ofReal (r j) := by sorry

end MatrixAnalytic.MinimalSolutions
