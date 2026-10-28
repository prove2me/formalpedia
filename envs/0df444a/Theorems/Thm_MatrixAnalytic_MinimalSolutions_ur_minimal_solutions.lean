-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_ur_minimal_solutions
-- name    : MatrixAnalytic.MinimalSolutions.ur_minimal_solutions
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T12:37:29.270589+00:00
-- url     : https://prove2.me/theorems/ab5eb871-ca0c-4674-b313-38bfeba6cf3b
-- title:
--   Theorem 8.1.4 (8.13), (8.14), and (8.16): minimal solutions for U and R
-- statement:
--   For the exact QBD target of Theorem 8.1.4, prove the U/R system (8.13), the U equation and minimality (8.14), and the R quadratic equation and minimality (8.16), under the same stochasticity and irreducibility hypotheses.
-- source:
--   Source-faithful sub-conjunction of MatrixAnalytic.MinimalSolutions.minimal_solutions, theorem dfc9dab6-aedd-4f4b-902b-0a1d52c91f85; Latouche and Ramaswami, 1999, Theorem 8.1.4.

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal
open MatrixAnalytic.MinimalSolutions

theorem MatrixAnalytic.MinimalSolutions.ur_minimal_solutions {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ((∀ i j, seriesInvE (matU (qbdP B A₀ A₁ A₂)) i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matU (qbdP B A₀ A₁ A₂) = ennMat A₁ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₂) ∧
      matR (qbdP B A₀ A₁ A₂) = matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂))) ∧
      ∀ X Z : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) → (∀ i j, 0 ≤ Z i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (ennMat Z) (ennMat A₂) →
        ennMat Z = matMulE (ennMat A₀) (seriesInvE (ennMat X)) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j ∧
          matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) ∧
    (matU (qbdP B A₀ A₁ A₂) = ennMat A₁ +
        matMulE (matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂)))) (ennMat A₂) ∧
      ∀ X : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (matMulE (ennMat A₀) (seriesInvE (ennMat X))) (ennMat A₂) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j) ∧
    ((∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matR (qbdP B A₀ A₁ A₂) = ennMat A₀ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₁) +
        matMulE (matMulE (matR (qbdP B A₀ A₁ A₂)) (matR (qbdP B A₀ A₁ A₂))) (ennMat A₂) ∧
      ∀ Z : ι → ι → ℝ, (∀ i j, 0 ≤ Z i j) →
        ennMat Z = ennMat A₀ + matMulE (ennMat Z) (ennMat A₁) +
          matMulE (matMulE (ennMat Z) (ennMat Z)) (ennMat A₂) →
        ∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) := by
  sorry
