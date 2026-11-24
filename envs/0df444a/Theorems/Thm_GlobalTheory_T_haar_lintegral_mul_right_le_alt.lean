-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_lintegral_mul_right_le_alt
-- name    : GlobalTheory.T.haar_lintegral_mul_right_le_alt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:41:48.019909+00:00
-- url     : https://prove2.me/theorems/17bd80a9-33dd-4195-ba5b-bb902f68b1e4
-- title:
--   T: haar lintegral mul right le alt
-- statement:
--   The T construction uses the haar lintegral mul right le alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLeStatement
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

theorem GlobalTheory.T.haar_lintegral_mul_right_le_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal, Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by sorry
