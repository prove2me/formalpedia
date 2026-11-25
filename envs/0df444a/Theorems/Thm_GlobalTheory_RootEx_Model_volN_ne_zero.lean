-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_volN_ne_zero
-- name    : GlobalTheory.RootEx.Model.volN_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:41.147807+00:00
-- url     : https://prove2.me/theorems/a2b0558c-88e3-46d8-baaf-07271cf7639b
-- title:
--   Model: vol N ne zero
-- statement:
--   The Model construction uses the vol N ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L222-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L222-L229

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
variable [MeasurableSpace k]

theorem GlobalTheory.RootEx.Model.volN_ne_zero (ν : Measure k) [SigmaFinite ν] (hν : ν ≠ 0) (p : ℕ) : volN ν n c p ≠ 0 := by sorry
