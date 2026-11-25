-- Prove2me | Theorems.Thm_GlobalTheory_expNegTop_inj_of_eq
-- name    : GlobalTheory.expNegTop_inj_of_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:37.920175+00:00
-- url     : https://prove2.me/theorems/28af63ee-ee50-43d5-a2b4-17a4b4ca5521
-- title:
--   Global Theory: exp Neg Top inj of eq
-- statement:
--   The Global Theory construction uses the exp Neg Top inj of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L10-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsAlgClosedAddValuationIsAdicComplete
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

theorem GlobalTheory.expNegTop_inj_of_eq {a b : WithTop ℚ} (h : expNegTop a = expNegTop b) : a = b := by sorry
