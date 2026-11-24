-- Prove2me | Theorems.Thm_GlobalTheory_T_module_flat_mvPowerSeries_of_isNoetherianRing
-- name    : GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:53:12.123715+00:00
-- url     : https://prove2.me/theorems/af2046ed-b159-4573-912f-8e4101948551
-- title:
--   T: module flat mv Power Series of is Noetherian Ring
-- statement:
--   The T construction uses the module flat mv Power Series of is Noetherian Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatMvPowerSeriesOfIsNoetherianRingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatMvPowerSeriesOfIsNoetherianRingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by sorry
