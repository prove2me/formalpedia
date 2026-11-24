-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_mem_map_C_of_coeff_mem
-- name    : GlobalTheory.mvPowerSeries_mem_map_C_of_coeff_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:12.348997+00:00
-- url     : https://prove2.me/theorems/410dd36c-5452-4f0d-8dd8-ad1529a33d45
-- title:
--   Global Theory: mv Power Series mem map C of coeff mem
-- statement:
--   The Global Theory construction uses the mv Power Series mem map C of coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesMemMapCOfCoeffMem.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesMemMapCOfCoeffMem.lean#L15-L34

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

theorem GlobalTheory.mvPowerSeries_mem_map_C_of_coeff_mem {σ R : Type} [CommRing R] (I : Ideal R)
    (hI : I.FG) (g : MvPowerSeries σ R) (hg : ∀ n, MvPowerSeries.coeff n g ∈ I) :
    g ∈ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) I := by sorry
