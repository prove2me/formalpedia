-- Prove2me | Theorems.Thm_GlobalTheory_SW_FourierJ_Row_qv_smul
-- name    : GlobalTheory.SW.FourierJ.Row.qv_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:50.434979+00:00
-- url     : https://prove2.me/theorems/b8afda40-6ed1-5dfb-8ed5-72cb1b6860aa
-- title:
--   Row: qv smul
-- statement:
--   The Row construction uses the qv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PoissonSummationThetaSeriesRowTermCoset.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PoissonSummationThetaSeriesRowTermCoset.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ GlobalTheory.SW.FourierJ.Row
variable {ι : Type} [Fintype ι]
omit [Fintype ι]

theorem GlobalTheory.SW.FourierJ.Row.qv_smul (v : ι → ℚ) (r : ℚ) : qv (r • v) = (r : ℂ) • qv v := by sorry
