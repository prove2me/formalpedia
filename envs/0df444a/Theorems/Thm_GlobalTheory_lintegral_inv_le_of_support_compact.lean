-- Prove2me | Theorems.Thm_GlobalTheory_lintegral_inv_le_of_support_compact
-- name    : GlobalTheory.lintegral_inv_le_of_support_compact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:14.752193+00:00
-- url     : https://prove2.me/theorems/edf637fc-f1f4-405b-98de-388a12a10b0b
-- title:
--   Global Theory: lintegral inv le of support compact
-- statement:
--   The Global Theory construction uses the lintegral inv le of support compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralInvLeOfSupportCompact.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralInvLeOfSupportCompact.lean#L6-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Pointwise
open GlobalTheory

theorem GlobalTheory.lintegral_inv_le_of_support_compact : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by sorry
