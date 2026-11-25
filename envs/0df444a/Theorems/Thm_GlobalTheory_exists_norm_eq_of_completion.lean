-- Prove2me | Theorems.Thm_GlobalTheory_exists_norm_eq_of_completion
-- name    : GlobalTheory.exists_norm_eq_of_completion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:28.456642+00:00
-- url     : https://prove2.me/theorems/66645f0e-f5e7-44ac-8afc-5202f7547f28
-- title:
--   Global Theory: exists norm eq of completion
-- statement:
--   The Global Theory construction uses the exists norm eq of completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L33-L45

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

theorem GlobalTheory.exists_norm_eq_of_completion {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : UniformSpace.Completion K) : ∃ y : K, ‖x‖ = ‖y‖ := by sorry
