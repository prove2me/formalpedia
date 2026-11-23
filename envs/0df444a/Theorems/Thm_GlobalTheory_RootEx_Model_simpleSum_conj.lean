-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_simpleSum_conj
-- name    : GlobalTheory.RootEx.Model.simpleSum_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:47.050954+00:00
-- url     : https://prove2.me/theorems/f09375d6-05ec-4dc4-a6a9-9b29f38509d1
-- title:
--   Model: simple Sum conj
-- statement:
--   The Model construction uses the simple Sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L117-L124

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

theorem GlobalTheory.RootEx.Model.simpleSum_conj (u : GL (n ⊕ Fin c) k) (g : GL n k) :
    simpleSum ((embX c g)⁻¹ * u * embX c g) = simpleSum u := by sorry
