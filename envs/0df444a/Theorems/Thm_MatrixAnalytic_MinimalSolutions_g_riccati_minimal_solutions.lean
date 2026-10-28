-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_g_riccati_minimal_solutions
-- name    : MatrixAnalytic.MinimalSolutions.g_riccati_minimal_solutions
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:37:30.714968+00:00
-- url     : https://prove2.me/theorems/65589efa-80b2-4f3c-ac56-236fa2ea4f73
-- title:
--   Theorem 8.1.4 (8.15): G as the minimal nonnegative Riccati solution
-- statement:
--   For the exact QBD target of Theorem 8.1.4, prove that the first-passage matrix G is finite, solves the quadratic equation (8.15), and is entrywise below every nonnegative real solution.
-- source:
--   Exact (8.15) sub-conjunction of MatrixAnalytic.MinimalSolutions.minimal_solutions, theorem dfc9dab6-aedd-4f4b-902b-0a1d52c91f85; Latouche and Ramaswami, 1999, Theorem 8.1.4.

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal
open MatrixAnalytic.MinimalSolutions

theorem MatrixAnalytic.MinimalSolutions.g_riccati_minimal_solutions {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matG (qbdP B A₀ A₁ A₂) = ennMat A₂ + matMulE (ennMat A₁) (matG (qbdP B A₀ A₁ A₂)) +
        matMulE (ennMat A₀) (matMulE (matG (qbdP B A₀ A₁ A₂)) (matG (qbdP B A₀ A₁ A₂))) ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = ennMat A₂ + matMulE (ennMat A₁) (ennMat Y) +
          matMulE (ennMat A₀) (matMulE (ennMat Y) (ennMat Y)) →
        ∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≤ ennMat Y i j := by
  sorry
