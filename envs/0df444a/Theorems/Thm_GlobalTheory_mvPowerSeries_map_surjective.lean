-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_map_surjective
-- name    : GlobalTheory.mvPowerSeries_map_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:17.205987+00:00
-- url     : https://prove2.me/theorems/78b28f51-0ab6-4a70-86bd-e45afa8516dd
-- title:
--   Global Theory: mv Power Series map surjective
-- statement:
--   The Global Theory construction uses the mv Power Series map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesMemMapCOfCoeffMem.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesMemMapCOfCoeffMem.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesMemMapCOfCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.mvPowerSeries_map_surjective {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) :
    Function.Surjective (MvPowerSeries.map (σ := σ) φ) := by sorry
