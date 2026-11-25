-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub
-- name    : GlobalTheory.ChartCmp.GaugeDiff.jeq_of_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:32:30.88353+00:00
-- url     : https://prove2.me/theorems/0d0ab3a6-5a10-4fc1-b95e-fe5387bf6d6a
-- title:
--   Gauge Diff: jeq of sub
-- statement:
--   The Gauge Diff construction uses the jeq of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L69-L73

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

theorem GlobalTheory.ChartCmp.GaugeDiff.jeq_of_sub {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = f - g) :
    JEq m u v := by sorry
