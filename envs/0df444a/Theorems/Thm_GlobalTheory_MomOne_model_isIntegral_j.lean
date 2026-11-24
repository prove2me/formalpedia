-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_model_isIntegral_j
-- name    : GlobalTheory.MomOne.model_isIntegral_j
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:34:06.170678+00:00
-- url     : https://prove2.me/theorems/5dfd5efc-7992-4f17-8edc-6ec385774db4
-- title:
--   Mom One: model is Integral j
-- statement:
--   The Mom One construction uses the model is Integral j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGoodReductionAlgebraicWeierstrassModel.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGoodReductionAlgebraicWeierstrassModel.lean#L20-L33

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

theorem GlobalTheory.MomOne.model_isIntegral_j {d : ℕ} (hd : d ≠ 0) {L : PeriodPair} (hL : IsOK d L) :
    IsIntegral ℤ (GlobalTheory.latticeCurve L).j := by sorry
