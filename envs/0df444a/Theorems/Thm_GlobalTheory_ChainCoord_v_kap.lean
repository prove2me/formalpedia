-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_v_kap
-- name    : GlobalTheory.ChainCoord.v_kap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:00.801317+00:00
-- url     : https://prove2.me/theorems/8295d43e-5fc0-4176-a687-6321fca17959
-- title:
--   Chain Coord: v kap
-- statement:
--   The Chain Coord construction uses the v kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L196-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L196-L200

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
variable {C : Type} [Field C]

theorem GlobalTheory.ChainCoord.v_kap {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hv : v (l : C) = 1) (s : ℕ) :
    ((-((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v (kap C l s) := by sorry
