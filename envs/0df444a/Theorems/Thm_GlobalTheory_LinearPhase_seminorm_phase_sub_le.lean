-- Prove2me | Theorems.Thm_GlobalTheory_LinearPhase_seminorm_phase_sub_le
-- name    : GlobalTheory.LinearPhase.seminorm_phase_sub_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:10:40.667146+00:00
-- url     : https://prove2.me/theorems/2b401dbb-f627-4380-81c4-4bd472a391ae
-- title:
--   Linear Phase: seminorm phase sub le
-- statement:
--   The Linear Phase construction uses the seminorm phase sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormLinearPhaseSecondOrderLe.lean#L10-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormLinearPhaseSecondOrderLe.lean#L10-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormLinearPhaseSecondOrderLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory GlobalTheory.LinearPhase
open Complex GlobalTheory.CharFormDeriv

theorem GlobalTheory.LinearPhase.seminorm_phase_sub_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by sorry
