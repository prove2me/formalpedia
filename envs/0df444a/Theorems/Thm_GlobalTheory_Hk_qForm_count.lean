-- Prove2me | Theorems.Thm_GlobalTheory_Hk_qForm_count
-- name    : GlobalTheory.Hk.qForm_count
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:33.976192+00:00
-- url     : https://prove2.me/theorems/53741d66-310b-41b6-be1a-71bd8ff6e0be
-- title:
--   Hk: q Form count
-- statement:
--   The Hk construction uses the q Form count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L215-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L215-L326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.qForm_count : ∀ α γ l θ₁ θ₂ x : ℝ, 1 ≤ α → 1 ≤ γ → 1 ≤ x →
    {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.Finite ∧
    |(({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.ncard : ℕ) : ℝ) - Real.pi / Real.sqrt (α * γ) * x|
      ≤ 10 * Real.sqrt x := by sorry
