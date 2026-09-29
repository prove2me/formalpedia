-- Prove2me | Theorems.Thm_LinearOptimization_network_basis_inverse_integer
-- name    : LinearOptimization.network_basis_inverse_integer
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T04:15:06.662253+00:00
-- url     : https://prove2.me/theorems/87e66b67-757f-419b-a0c6-65b628c14e37
-- title:
--   Integer inverse of a network basis matrix
-- statement:
--   Let a directed network have $n+1$ vertices and $m$ arcs. Delete one row from its node–arc incidence matrix, and select any $n$ linearly independent columns to form a square basis matrix $B$. Then every entry of the inverse is integral:
--
--   $$
--   \forall i,j,\quad (B^{-1})_{ij}\in\mathbb Z.
--   $$
--
--   This is the algebraic integrality property behind integer primal and dual basic solutions in network-flow linear programs.
--
--   **Formalization Note** The selected columns are represented by an embedding and linear independence is expressed by `IsStdBasis`.
-- source:
--   Dimitris Bertsimas and John N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, p. 289, Theorem 7.5(a). https://pdfcoffee.com/introduction-to-linear-optimization-by-dimitris-john-n-tsitsiklis-pdf-free.html

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Definitions.Def_BasicSolution
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

open LinearOptimization

theorem LinearOptimization.network_basis_inverse_integer {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (B : Fin n ↪ Fin m)
    (hB : IsStdBasis (truncatedIncidence arcs) B) :
    ∀ i j, ∃ z : ℤ,
      (basisMatrix (truncatedIncidence arcs) B)⁻¹ i j = (z : ℝ) := by sorry
