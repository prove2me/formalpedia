-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_ur_path_factorization
-- name    : MatrixAnalytic.MinimalSolutions.ur_path_factorization
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T14:48:46.839898+00:00
-- url     : https://prove2.me/theorems/9059659f-c742-4ebf-9884-19e609ff47a6
-- title:
--   Expected-visits path factorization for the QBD rate matrix
-- statement:
--   Under the stochasticity and irreducibility assumptions of an exact QBD, the expected-visit matrix matR is finite entrywise and equals the level-up block A₀ multiplied by the series inverse of the first-return matrix matU.
-- source:
--   Source-faithful sub-conjunction of MatrixAnalytic.MinimalSolutions.ur_minimal_solutions (target ab5eb871-ca0c-4674-b313-38bfeba6cf3b), Theorem 8.1.4 of Latouche and Ramaswami (1999).

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal
open MatrixAnalytic.MinimalSolutions

theorem MatrixAnalytic.MinimalSolutions.ur_path_factorization {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matR (qbdP B A₀ A₁ A₂) = matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂))) := by sorry
