-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_simple_entry_mul
-- name    : GlobalTheory.RootEx.Model.simple_entry_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:16.894273+00:00
-- url     : https://prove2.me/theorems/e1bf6cc0-db74-4645-a28d-1fb64e989b82
-- title:
--   Model: simple entry mul
-- statement:
--   The Model construction uses the simple entry mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L61-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L61-L84

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

theorem GlobalTheory.RootEx.Model.simple_entry_mul {p : ℕ} {g h : GL (n ⊕ Fin c) k} (hg : InN p g) (hh : InN p h) (i j : Fin c)
    (hij : j.val = i.val + 1) : (g * h).val (Sum.inr i) (Sum.inr j) =
      g.val (Sum.inr i) (Sum.inr j) + h.val (Sum.inr i) (Sum.inr j) := by sorry
