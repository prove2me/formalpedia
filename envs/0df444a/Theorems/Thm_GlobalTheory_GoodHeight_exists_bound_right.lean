-- Prove2me | Theorems.Thm_GlobalTheory_GoodHeight_exists_bound_right
-- name    : GlobalTheory.GoodHeight.exists_bound_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:08.659953+00:00
-- url     : https://prove2.me/theorems/8af66778-e8d5-4aae-8ea0-8f0e8d1b5aba
-- title:
--   Good Height: exists bound right
-- statement:
--   The Good Height construction uses the exists bound right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L74-L91

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

theorem GlobalTheory.GoodHeight.exists_bound_right : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by sorry
