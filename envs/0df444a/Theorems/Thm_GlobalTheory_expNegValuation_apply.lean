-- Prove2me | Theorems.Thm_GlobalTheory_expNegValuation_apply
-- name    : GlobalTheory.expNegValuation_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:47:45.375721+00:00
-- url     : https://prove2.me/theorems/78098874-b29d-4544-92ec-5b134cf9e926
-- title:
--   Global Theory: exp Neg Valuation apply
-- statement:
--   The Global Theory construction uses the exp Neg Valuation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNnrealValuationOfAddValuation.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNnrealValuationOfAddValuation.lean#L58-L59

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

theorem GlobalTheory.expNegValuation_apply {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := by sorry
