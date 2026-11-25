-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_affPt_block
-- name    : GlobalTheory.RootEx.Model.affPt_block
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:39.983045+00:00
-- url     : https://prove2.me/theorems/84db985d-888c-449b-ae71-ccb9ddb062d3
-- title:
--   Model: aff Pt block
-- statement:
--   The Model construction uses the aff Pt block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L150-L153

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

theorem GlobalTheory.RootEx.Model.affPt_block {n' : Type*} [Fintype n'] [DecidableEq n'] (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n) (s : n') :
    affPt p x₀ e (Sum.inl r) (Sum.inl s) = x₀ r s := by sorry
