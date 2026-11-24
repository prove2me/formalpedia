-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_integral_superposition
-- name    : GlobalTheory.T.schwartz_integral_superposition
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:15.998794+00:00
-- url     : https://prove2.me/theorems/7f2bdc83-abe8-4b21-b382-9e7c58a8fb29
-- title:
--   T: schwartz integral superposition
-- statement:
--   The T construction uses the schwartz integral superposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperpositionStatement.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperpositionStatement.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperpositionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_integral_superposition : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by sorry
