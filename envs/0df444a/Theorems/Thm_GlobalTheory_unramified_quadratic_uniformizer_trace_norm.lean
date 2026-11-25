-- Prove2me | Theorems.Thm_GlobalTheory_unramified_quadratic_uniformizer_trace_norm
-- name    : GlobalTheory.unramified_quadratic_uniformizer_trace_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:24.68906+00:00
-- url     : https://prove2.me/theorems/34e0a312-e967-412c-ba27-ff3dbf13f4df
-- title:
--   Global Theory: unramified quadratic uniformizer trace norm
-- statement:
--   The Global Theory construction uses the unramified quadratic uniformizer trace norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticUniformizerTraceNorm.lean#L10-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticUniformizerTraceNorm.lean#L10-L68

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticUniformizerTraceNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory
open GroundTheory.LocalField IsLocalRing

theorem GlobalTheory.unramified_quadratic_uniformizer_trace_norm : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], GroundTheory.LocalField.ramificationIndex K L = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by sorry
