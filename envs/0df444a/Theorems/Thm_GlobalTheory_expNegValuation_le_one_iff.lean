-- Prove2me | Theorems.Thm_GlobalTheory_expNegValuation_le_one_iff
-- name    : GlobalTheory.expNegValuation_le_one_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:39.086274+00:00
-- url     : https://prove2.me/theorems/ee9b8b1f-db4d-4896-974e-35bf15ff4104
-- title:
--   Global Theory: exp Neg Valuation le one iff
-- statement:
--   The Global Theory construction uses the exp Neg Valuation le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNnrealValuationOfAddValuation.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNnrealValuationOfAddValuation.lean#L61-L63

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

theorem GlobalTheory.expNegValuation_le_one_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by sorry
