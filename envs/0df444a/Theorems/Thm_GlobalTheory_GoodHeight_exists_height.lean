-- Prove2me | Theorems.Thm_GlobalTheory_GoodHeight_exists_height
-- name    : GlobalTheory.GoodHeight.exists_height
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:25.166608+00:00
-- url     : https://prove2.me/theorems/56d9d70c-d977-4db4-aad0-7a1522654d2c
-- title:
--   Good Height: exists height
-- statement:
--   The Good Height construction uses the exists height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L150-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L150-L357

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight

theorem GlobalTheory.GoodHeight.exists_height : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ∀ s : ℂ, -(1/2 : ℝ) ≤ s.re → s.re ≤ 3 → |s.im| = T' → LFunction χ s ≠ 0 ∧ ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C * Real.log (N * T) ^ 2 := by sorry
