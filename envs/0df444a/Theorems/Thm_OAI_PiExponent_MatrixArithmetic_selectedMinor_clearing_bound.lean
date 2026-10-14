-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_clearing_bound
-- name    : OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T15:35:24.297765+00:00
-- url     : https://prove2.me/theorems/922467c8-68a8-4256-9a01-ee896d0f153e
-- title:
--   A denominator-clearing lower bound for a selected interpolation minor
-- statement:
--   For the original truncated-logarithm interpolation matrix, choose a square minor with nonzero determinant. Under the stated positive integer denominator and weight assumptions, its logarithmic determinant is bounded below by the negative row-count times the logarithm of the common denominator, minus the selected column cost, plus the row cost. The definitions and indices are exactly those of the source theorem.
--
--   Here $m,K\in\mathbb{N}$; $w_0,v_0,\theta,F,H\in\mathbb{R}$; $p:\operatorname{Fin}(m)\to\mathbb{Z}$; $q:\operatorname{Fin}(m)\to\mathbb{N}$ with $q_i\ge 2$; $w_0>0$; and the selection maps the source row index set to the source column index set.  If the selected minor $M_{\mathrm{sel}}$ has nonzero determinant, then, with $r$ its row count, $D$ the source common denominator, and $C_{\mathrm{col}},C_{\mathrm{row}}$ the source column and row costs,
--
--   $$-r\log D-C_{\mathrm{col}}+C_{\mathrm{row}}\leq\log\lVert\det M_{\mathrm{sel}}\rVert.$$
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L337-L358

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_entry_truncatedLog_cleared_gaussian

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic
open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (denominator q (truncationOrders q F v0) H) -
      columnCost q selection + rowCost K v0 θ q H ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ := by
  sorry
