-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_Model_secondForm_tautPairGram
-- name    : GlobalTheory.HermFrame.Model.secondForm_tautPairGram
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:45.487603+00:00
-- url     : https://prove2.me/theorems/9b9ad9e8-ff43-42f2-aab1-939227bd8b20
-- title:
--   Model: second Form taut Pair Gram
-- statement:
--   The Model construction uses the second Form taut Pair Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L158-L164

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

theorem GlobalTheory.HermFrame.Model.secondForm_tautPairGram (ξ : ℂ) : secondForm tautPairGram 0 ξ = of fun _ _ => ξ := by sorry
