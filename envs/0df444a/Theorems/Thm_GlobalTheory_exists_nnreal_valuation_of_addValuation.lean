-- Prove2me | Theorems.Thm_GlobalTheory_exists_nnreal_valuation_of_addValuation
-- name    : GlobalTheory.exists_nnreal_valuation_of_addValuation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:44.097413+00:00
-- url     : https://prove2.me/theorems/1a4f6f65-4d14-5bb6-b546-9ba3846d8b63
-- title:
--   Global Theory: exists nnreal valuation of add Valuation
-- statement:
--   The Global Theory construction uses the exists nnreal valuation of add Valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNnrealValuationOfAddValuation.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNnrealValuationOfAddValuation.lean#L65-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped NNReal

theorem GlobalTheory.exists_nnreal_valuation_of_addValuation :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by sorry
