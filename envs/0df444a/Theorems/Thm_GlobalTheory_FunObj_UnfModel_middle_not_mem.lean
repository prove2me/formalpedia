-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_UnfModel_middle_not_mem
-- name    : GlobalTheory.FunObj.UnfModel.middle_not_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:01.052961+00:00
-- url     : https://prove2.me/theorems/f88033eb-01b3-4231-8f2b-9a1fb7fe212c
-- title:
--   Unf Model: middle not mem
-- statement:
--   The Unf Model construction uses the middle not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L36-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

theorem GlobalTheory.FunObj.UnfModel.middle_not_mem (ρ : ℕ) (u : n → k) (hu : u ≠ 0) : rowE (2 * ρ + 1) (ρ + 1) u ∉ symN k n (2 * ρ + 1) := by sorry
