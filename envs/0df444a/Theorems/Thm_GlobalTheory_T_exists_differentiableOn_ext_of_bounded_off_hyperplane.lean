-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_differentiableOn_ext_of_bounded_off_hyperplane
-- name    : GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:34:01.181421+00:00
-- url     : https://prove2.me/theorems/3c53d3eb-5d54-4884-b84d-01299b026f8a
-- title:
--   T: exists differentiable On ext of bounded off hyperplane
-- statement:
--   The T construction uses the exists differentiable On ext of bounded off hyperplane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionCoordinateHyperplaneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionCoordinateHyperplaneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionCoordinateHyperplane
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionCoordinateHyperplaneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by sorry
