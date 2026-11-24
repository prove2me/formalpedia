-- Prove2me | Theorems.Thm_GlobalTheory_uniform_log_expansion_of_pointwise
-- name    : GlobalTheory.uniform_log_expansion_of_pointwise
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:22.927884+00:00
-- url     : https://prove2.me/theorems/4c7b4704-7334-4511-9dde-2d91c5874b48
-- title:
--   Global Theory: uniform log expansion of pointwise
-- statement:
--   The Global Theory construction uses the uniform log expansion of pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/UniformLogExpansionOfPointwise.lean#L135-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/UniformLogExpansionOfPointwise.lean#L135-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UniformLogExpansionOfPointwise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

theorem GlobalTheory.uniform_log_expansion_of_pointwise :
    (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by sorry
