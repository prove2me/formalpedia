-- Prove2me | Theorems.Thm_GlobalTheory_NearZeroDeriv_inv_sq_le_re
-- name    : GlobalTheory.NearZeroDeriv.inv_sq_le_re
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:32:43.082617+00:00
-- url     : https://prove2.me/theorems/b39ad0a2-dc94-4e2a-a46c-8311d8aae83d
-- title:
--   Near Zero Deriv: inv sq le re
-- statement:
--   The Near Zero Deriv construction uses the inv sq le re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L121-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv

theorem GlobalTheory.NearZeroDeriv.inv_sq_le_re {s w : ℂ} {r : ℝ} (m : ℕ) (h : r ≤ (s - w).re) :
    r * ((m : ℝ) / ‖s - w‖ ^ 2) ≤ ((m : ℂ) / (s - w)).re := by sorry
