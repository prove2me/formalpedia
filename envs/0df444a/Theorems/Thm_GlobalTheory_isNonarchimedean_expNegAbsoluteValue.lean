-- Prove2me | Theorems.Thm_GlobalTheory_isNonarchimedean_expNegAbsoluteValue
-- name    : GlobalTheory.isNonarchimedean_expNegAbsoluteValue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:37.629946+00:00
-- url     : https://prove2.me/theorems/96389af7-d423-4521-81c6-3811e1f654a0
-- title:
--   Global Theory: is Nonarchimedean exp Neg Absolute Value
-- statement:
--   The Global Theory construction uses the is Nonarchimedean exp Neg Absolute Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L25-L31

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

theorem GlobalTheory.isNonarchimedean_expNegAbsoluteValue {F : Type} [Field F]
    (v : AddValuation F (WithTop ℚ)) : IsNonarchimedean (expNegAbsoluteValue v) := by sorry
