-- Prove2me | Theorems.Thm_GlobalTheory_cauchy_slice_removable_extension
-- name    : GlobalTheory.cauchy_slice_removable_extension
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:45.707417+00:00
-- url     : https://prove2.me/theorems/b3781658-d595-48cd-910d-8f4be168e53e
-- title:
--   Global Theory: cauchy slice removable extension
-- statement:
--   The Global Theory construction uses the cauchy slice removable extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CauchySliceEqRemovableExtension.lean#L6-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CauchySliceEqRemovableExtension.lean#L6-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CauchySliceEqRemovableExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory

theorem GlobalTheory.cauchy_slice_removable_extension :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by sorry
