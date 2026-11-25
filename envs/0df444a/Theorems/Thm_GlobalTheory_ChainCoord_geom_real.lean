-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_geom_real
-- name    : GlobalTheory.ChainCoord.geom_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:34.709325+00:00
-- url     : https://prove2.me/theorems/d6b29a2d-28af-4cbd-9787-886c9bd1e772
-- title:
--   Chain Coord: geom real
-- statement:
--   The Chain Coord construction uses the geom real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L165-L172

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

theorem GlobalTheory.ChainCoord.geom_real {l : ℕ} (hl : 3 ≤ l) (s : ℕ) :
    ((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ) =
      (((l : ℝ) ^ 2) ^ s - 1) * (1 / ((l : ℝ) ^ 2 - 1)) := by sorry
