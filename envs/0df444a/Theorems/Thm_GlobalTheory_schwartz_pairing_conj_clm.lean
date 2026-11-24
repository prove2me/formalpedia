-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_pairing_conj_clm
-- name    : GlobalTheory.schwartz_pairing_conj_clm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:49.93881+00:00
-- url     : https://prove2.me/theorems/56f04dbd-a222-4ebb-a2f2-88ac0c3af0e5
-- title:
--   Global Theory: schwartz pairing conj clm
-- statement:
--   The Global Theory construction uses the schwartz pairing conj clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzInnerProductContinuous.lean#L6-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzInnerProductContinuous.lean#L6-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzInnerProductContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.schwartz_pairing_conj_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by sorry
