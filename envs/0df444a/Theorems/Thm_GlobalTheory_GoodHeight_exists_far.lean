-- Prove2me | Theorems.Thm_GlobalTheory_GoodHeight_exists_far
-- name    : GlobalTheory.GoodHeight.exists_far
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:14.871823+00:00
-- url     : https://prove2.me/theorems/f3c093f5-4c90-444f-9e2c-d33183589144
-- title:
--   Good Height: exists far
-- statement:
--   The Good Height construction uses the exists far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L8-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L8-L48

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

theorem GlobalTheory.GoodHeight.exists_far (S : Finset ℝ) (T : ℝ) : ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
    ∀ x ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - T'| := by sorry
