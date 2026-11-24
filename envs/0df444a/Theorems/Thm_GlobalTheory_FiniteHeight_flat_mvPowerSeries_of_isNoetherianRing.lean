-- Prove2me | Theorems.Thm_GlobalTheory_FiniteHeight_flat_mvPowerSeries_of_isNoetherianRing
-- name    : GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:28.827095+00:00
-- url     : https://prove2.me/theorems/8c75233e-994c-4f91-9c67-6c3067a6e2f4
-- title:
--   Finite Height: flat mv Power Series of is Noetherian Ring
-- statement:
--   The Finite Height construction uses the flat mv Power Series of is Noetherian Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatMvPowerSeriesOfIsNoetherianRing.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatMvPowerSeriesOfIsNoetherianRing.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.FiniteHeight

theorem GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) := by sorry
