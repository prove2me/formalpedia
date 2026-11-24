-- Prove2me | Theorems.Thm_GlobalTheory_haar_lintegral_mul_right_le
-- name    : GlobalTheory.haar_lintegral_mul_right_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:32.264042+00:00
-- url     : https://prove2.me/theorems/323185a1-bdf3-48ee-af64-1c010bc0a331
-- title:
--   Global Theory: haar lintegral mul right le
-- statement:
--   The Global Theory construction uses the haar lintegral mul right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLe.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLe.lean#L46-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory

theorem GlobalTheory.haar_lintegral_mul_right_le :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
      [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H),
      μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal,
        Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by sorry
