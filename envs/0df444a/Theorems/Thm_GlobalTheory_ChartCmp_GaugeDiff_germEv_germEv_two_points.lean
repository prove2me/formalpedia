-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_germEv_germEv_two_points
-- name    : GlobalTheory.ChartCmp.GaugeDiff.germEv_germEv_two_points
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:05.565384+00:00
-- url     : https://prove2.me/theorems/c23374b0-caab-59ba-b828-87046dc80e06
-- title:
--   Gauge Diff: germ Ev germ Ev two points
-- statement:
--   The Gauge Diff construction uses the germ Ev germ Ev two points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L111-L113

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
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.ChartCmp.GaugeDiff.germEv_germEv_two_points {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d) (ha : GP a) (hb : GP b)
    (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by sorry
