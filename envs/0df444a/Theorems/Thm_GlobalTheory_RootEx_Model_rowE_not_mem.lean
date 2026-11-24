-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_rowE_not_mem
-- name    : GlobalTheory.RootEx.Model.rowE_not_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:19.19399+00:00
-- url     : https://prove2.me/theorems/de52939d-0643-4d30-9dc8-a4ce2729fb72
-- title:
--   Model: row E not mem
-- statement:
--   The Model construction uses the row E not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L54-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.Model.rowE_not_mem (l : Fin c) (u : n → k) (hu : u ≠ 0) : rowE c (l.val + 1) u ∉ N k n c (l.val + 1) := by sorry
