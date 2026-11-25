-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_high_real
-- name    : GlobalTheory.ChainCoord.high_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:20.97607+00:00
-- url     : https://prove2.me/theorems/ad840685-6f84-4fa9-a616-8a3ae1238bd5
-- title:
--   Chain Coord: high real
-- statement:
--   The Chain Coord construction uses the high real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L174-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L174-L188

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord

theorem GlobalTheory.ChainCoord.high_real {l : ℕ} (hl : 3 ≤ l) (k : ℕ) :
    1 + 1 / ((l : ℝ) ^ 2 - 1) ≤
      (1 - ((k + 3 : ℕ) : ℝ)) + ((l ^ (k + 3) : ℕ) : ℝ) * (1 / ((l : ℝ) ^ 2 - 1)) := by sorry
