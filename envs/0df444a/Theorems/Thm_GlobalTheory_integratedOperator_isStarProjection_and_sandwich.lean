-- Prove2me | Theorems.Thm_GlobalTheory_integratedOperator_isStarProjection_and_sandwich
-- name    : GlobalTheory.integratedOperator_isStarProjection_and_sandwich
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:43.021821+00:00
-- url     : https://prove2.me/theorems/ed29d970-7b40-4e6f-9f88-9d17d2646ba1
-- title:
--   Global Theory: integrated Operator is Star Projection and sandwich
-- statement:
--   The Global Theory construction uses the integrated Operator is Star Projection and sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegratedOperatorIsStarProjectionAndSandwich.lean#L21-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegratedOperatorIsStarProjectionAndSandwich.lean#L21-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegratedOperatorIsStarProjectionAndSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.integratedOperator_isStarProjection_and_sandwich :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [SigmaFinite μ] [μ.IsInvInvariant] (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ (φ m : G → ℂ), Integrable φ μ → (∀ g, star (φ g⁻¹) = φ g) → (∀ x y : G, ∫ g, φ g * φ (x⁻¹ * g⁻¹ * y) ∂μ = m x * φ y) → m 1 = 1 → ∀ P : Hp →L[ℂ] Hp, (∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ) → IsStarProjection P ∧ ∀ x : G, P ∘L π x ∘L P = m x • P := by sorry
