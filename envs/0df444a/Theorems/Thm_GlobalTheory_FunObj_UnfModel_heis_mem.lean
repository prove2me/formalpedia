-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_UnfModel_heis_mem
-- name    : GlobalTheory.FunObj.UnfModel.heis_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:45.509869+00:00
-- url     : https://prove2.me/theorems/ae43e7b0-3553-4661-a2dc-f8661febdd38
-- title:
--   Unf Model: heis mem
-- statement:
--   The Unf Model construction uses the heis mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MiddleNotMem.lean#L32-L34

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

theorem GlobalTheory.FunObj.UnfModel.heis_mem (ρ : ℕ) (u β : n → k) : rowE (2 * ρ) ρ u ∈ symN k n (2 * ρ) ∧ colE (2 * ρ) (ρ + 1) β ∈ symN k n (2 * ρ) := by sorry
