-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_free_last
-- name    : GlobalTheory.RootEx.Model.free_last
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:22.367016+00:00
-- url     : https://prove2.me/theorems/e16b1aa6-28bd-5827-8387-b427bed0f24b
-- title:
--   Model: free last
-- statement:
--   The Model construction uses the free last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L155-L158

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

theorem GlobalTheory.RootEx.Model.free_last {n' : Type*} (p : ℕ) (hp : p ≤ c) (r : n ⊕ Fin c) :
    Free (n := n) (n' := n') p (r, Sum.inr (Fin.last c)) := by sorry
