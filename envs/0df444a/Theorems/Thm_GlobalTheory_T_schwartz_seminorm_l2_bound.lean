-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_seminorm_l2_bound
-- name    : GlobalTheory.T.schwartz_seminorm_l2_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:42.028799+00:00
-- url     : https://prove2.me/theorems/9c11fa85-ad47-5c1f-82aa-da5870529b99
-- title:
--   T: schwartz seminorm l2 bound
-- statement:
--   The T construction uses the schwartz seminorm l2 bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormL2BoundStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormL2BoundStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormL2Bound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormL2BoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_seminorm_l2_bound : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
        C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by sorry
