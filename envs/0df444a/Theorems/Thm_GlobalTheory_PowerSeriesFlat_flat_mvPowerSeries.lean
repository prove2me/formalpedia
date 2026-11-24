-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesFlat_flat_mvPowerSeries
-- name    : GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:12.533918+00:00
-- url     : https://prove2.me/theorems/9156c105-2f64-4c90-a446-5bba329a8812
-- title:
--   Power Series Flat: flat mv Power Series
-- statement:
--   The Power Series Flat construction uses the flat mv Power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatMvPowerSeries.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatMvPowerSeries.lean#L40-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PowerSeriesFlat

theorem GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) := by sorry
