-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_exists_model
-- name    : GlobalTheory.MomOne.exists_model
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:25.821936+00:00
-- url     : https://prove2.me/theorems/a7c3ff46-56ef-5bff-b40c-aef57582f828
-- title:
--   Mom One: exists model
-- statement:
--   The Mom One construction uses the exists model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGoodReductionAlgebraicWeierstrassModel.lean#L35-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGoodReductionAlgebraicWeierstrassModel.lean#L35-L69

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

theorem GlobalTheory.MomOne.exists_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by sorry
