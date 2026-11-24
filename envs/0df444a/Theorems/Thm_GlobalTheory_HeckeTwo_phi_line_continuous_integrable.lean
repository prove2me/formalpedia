-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_phi_line_continuous_integrable
-- name    : GlobalTheory.HeckeTwo.phi_line_continuous_integrable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:58.849213+00:00
-- url     : https://prove2.me/theorems/27a08e09-f30f-4fcb-ba26-daf7d9906fb2
-- title:
--   Hecke Two: phi line continuous integrable
-- statement:
--   The Hecke Two construction uses the phi line continuous integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoKernelPhiLineContinuousIntegrable.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoKernelPhiLineContinuousIntegrable.lean#L65-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory

theorem GlobalTheory.HeckeTwo.phi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by sorry
