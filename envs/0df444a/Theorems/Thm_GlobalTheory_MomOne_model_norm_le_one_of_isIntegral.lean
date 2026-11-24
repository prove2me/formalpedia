-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_model_norm_le_one_of_isIntegral
-- name    : GlobalTheory.MomOne.model_norm_le_one_of_isIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:34:17.213616+00:00
-- url     : https://prove2.me/theorems/47087347-99c9-4fb6-83e5-5a44ba7ddd3f
-- title:
--   Mom One: model norm le one of is Integral
-- statement:
--   The Mom One construction uses the model norm le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGoodReductionAlgebraicWeierstrassModel.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGoodReductionAlgebraicWeierstrassModel.lean#L11-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGoodReductionAlgebraicWeierstrassModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane
open GlobalTheory GlobalTheory.MomOne

theorem GlobalTheory.MomOne.model_norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by sorry
