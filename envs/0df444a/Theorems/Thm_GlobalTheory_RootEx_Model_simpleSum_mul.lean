-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_simpleSum_mul
-- name    : GlobalTheory.RootEx.Model.simpleSum_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:13.39703+00:00
-- url     : https://prove2.me/theorems/fb4f0a93-60a9-48f7-9d9e-c0be5d8a67c2
-- title:
--   Model: simple Sum mul
-- statement:
--   The Model construction uses the simple Sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L86-L93

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

theorem GlobalTheory.RootEx.Model.simpleSum_mul {p : ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (hh : h ∈ N k n c p) :
    simpleSum (g * h) = simpleSum g + simpleSum h := by sorry
