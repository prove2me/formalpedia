-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_mapPt_addOf
-- name    : GlobalTheory.ChartCmp.GaugeDiff.mapPt_addOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:41.401924+00:00
-- url     : https://prove2.me/theorems/0ad60080-db92-5078-bd6f-0696baa26288
-- title:
--   Gauge Diff: map Pt add Of
-- statement:
--   The Gauge Diff construction uses the map Pt add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L56-L58

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

theorem GlobalTheory.ChartCmp.GaugeDiff.mapPt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : GP a) (hb : GP b) :
    mapPt β (addOf F a b) = addOf (mapPt β F) (mapPt β a) (mapPt β b) := by sorry
