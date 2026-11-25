-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_map_ev1
-- name    : GlobalTheory.ChartCmp.GaugeDiff.map_ev1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:08.46359+00:00
-- url     : https://prove2.me/theorems/8c1fe895-ea81-5b53-8c38-63ea00c8a76c
-- title:
--   Gauge Diff: map ev1
-- statement:
--   The Gauge Diff construction uses the map ev1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L25-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.GaugeDiff
variable {R k : Type} [CommRing R] [CommRing k] {d : ℕ} (β : R →+* k)

theorem GlobalTheory.ChartCmp.GaugeDiff.map_ev1 {n : ℕ} (a : Pt R n d) (ha : GP a) (f : PS R 1 d) :
    MvPowerSeries.map β (ev ![a] f) = ev ![mapPt β a] (MvPowerSeries.map β f) := by sorry
