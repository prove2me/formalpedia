-- Prove2me | Theorems.Thm_GlobalTheory_FormalMul_mulF_map
-- name    : GlobalTheory.FormalMul.mulF_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:10.368144+00:00
-- url     : https://prove2.me/theorems/4f118af8-9517-47ac-baa6-c349287ed0aa
-- title:
--   Formal Mul: mul F map
-- statement:
--   The Formal Mul construction uses the mul F map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MulFConstAndMap.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MulFConstAndMap.lean#L18-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MulFConstAndMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.FormalMul

theorem GlobalTheory.FormalMul.mulF_map {T O : Type} [CommRing T] [CommRing O] (io : T →+* O) {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) :
    ∀ j, mulF (fun i => MvPowerSeries.map io (F i)) N j = MvPowerSeries.map io (mulF F N j) := by sorry
