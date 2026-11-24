-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_Model_blockQQ_eq
-- name    : GlobalTheory.HermFrame.Model.blockQQ_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:17.455451+00:00
-- url     : https://prove2.me/theorems/25855e9f-e405-43a2-ba4e-2936c64d4032
-- title:
--   Model: block QQ eq
-- statement:
--   The Model construction uses the block QQ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CurvSubQuotTautPairGram.lean#L20-L24

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

theorem GlobalTheory.HermFrame.Model.blockQQ_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockQQ K T = T.toBlocks₂₂ - T.toBlocks₂₁ * orthCoeff K := by sorry
