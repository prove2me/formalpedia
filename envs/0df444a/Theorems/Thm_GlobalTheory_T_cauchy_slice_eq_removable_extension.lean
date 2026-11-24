-- Prove2me | Theorems.Thm_GlobalTheory_T_cauchy_slice_eq_removable_extension
-- name    : GlobalTheory.T.cauchy_slice_eq_removable_extension
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:37.586951+00:00
-- url     : https://prove2.me/theorems/667f9127-af75-4c98-b2d9-96c64143af4c
-- title:
--   T: cauchy slice eq removable extension
-- statement:
--   The T construction uses the cauchy slice eq removable extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CauchySliceEqRemovableExtensionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CauchySliceEqRemovableExtensionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CauchySliceEqRemovableExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CauchySliceEqRemovableExtensionStatement
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

theorem GlobalTheory.T.cauchy_slice_eq_removable_extension : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by sorry
