-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_Model_curv_tautPairGram
-- name    : GlobalTheory.HermFrame.Model.curv_tautPairGram
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:03.057015+00:00
-- url     : https://prove2.me/theorems/0e0422d7-5275-43ff-aeea-5dc5fd86b4b7
-- title:
--   Model: curv taut Pair Gram
-- statement:
--   The Model construction uses the curv taut Pair Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L149-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem GlobalTheory.HermFrame.Model.curv_tautPairGram (z ξ η : ℂ) : curv tautPairGram z ξ η = 0 := by sorry
