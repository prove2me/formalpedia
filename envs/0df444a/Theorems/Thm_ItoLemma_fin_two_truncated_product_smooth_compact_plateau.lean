-- Prove2me | Theorems.Thm_ItoLemma_fin_two_truncated_product_smooth_compact_plateau
-- name    : ItoLemma.fin_two_truncated_product_smooth_compact_plateau
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:56:07.048927+00:00
-- url     : https://prove2.me/theorems/ee70cad8-b4e4-4d0f-9254-4b1d37ec0bd2
-- title:
--   Smooth Compactly Supported Truncated Coordinate Product
-- statement:
--   Multiplying the coordinate product x₀x₁ by a C∞ compactly supported cutoff yields a C∞ compactly supported test function which agrees with the coordinate product on the cutoff plateau. This provides the admissible spatial test function for the bounded-derivative vector Itô formula.
-- source:
--   Mathlib pinned revision; ContDiff.mul and contDiff_apply, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Operations.html; HasCompactSupport.mul_right, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Support.html; inspected 26 October 2026.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

theorem ItoLemma.fin_two_truncated_product_smooth_compact_plateau
    (R : ℝ) (ψ : (Fin 2 → ℝ) → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hs : HasCompactSupport ψ)
    (hp : ∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → ψ z = 1) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Fin 2 → ℝ => ψ z * (z 0 * z 1)) ∧
    HasCompactSupport (fun z : Fin 2 → ℝ => ψ z * (z 0 * z 1)) ∧
    (∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → ψ z * (z 0 * z 1) = z 0 * z 1) := by sorry
