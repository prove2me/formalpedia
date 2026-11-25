-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzSeminorm_linearPhase_second_order_le
-- name    : GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:02.294245+00:00
-- url     : https://prove2.me/theorems/43745fd4-b2c1-53a1-abaa-ab1567eb19f4
-- title:
--   T: schwartz Seminorm linear Phase second order le
-- statement:
--   The T construction uses the schwartz Seminorm linear Phase second order le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormLinearPhaseSecondOrderLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormLinearPhaseSecondOrderLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormLinearPhaseSecondOrderLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormLinearPhaseSecondOrderLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by sorry
