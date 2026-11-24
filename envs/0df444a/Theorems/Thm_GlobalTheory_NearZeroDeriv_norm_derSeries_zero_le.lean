-- Prove2me | Theorems.Thm_GlobalTheory_NearZeroDeriv_norm_derSeries_zero_le
-- name    : GlobalTheory.NearZeroDeriv.norm_derSeries_zero_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:32:37.029204+00:00
-- url     : https://prove2.me/theorems/8cd98d8c-4d4f-4d9e-b00a-43693c097f20
-- title:
--   Near Zero Deriv: norm der Series zero le
-- statement:
--   The Near Zero Deriv construction uses the norm der Series zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L127-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L127-L157

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

theorem GlobalTheory.NearZeroDeriv.norm_derSeries_zero_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (σ t : ℝ) (hσ : 1 < σ) :
    ‖derSeries c 0 (σ + t * I)‖ ≤
      (derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) 0 (σ + (0 : ℝ) * I)).re := by sorry
