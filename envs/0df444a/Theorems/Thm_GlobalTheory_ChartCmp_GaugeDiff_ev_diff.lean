-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_ev_diff
-- name    : GlobalTheory.ChartCmp.GaugeDiff.ev_diff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:01.096167+00:00
-- url     : https://prove2.me/theorems/f4510977-aac9-59ac-8dec-5d1239cc1427
-- title:
--   Gauge Diff: ev diff
-- statement:
--   The Gauge Diff construction uses the ev diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L123-L126

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

theorem GlobalTheory.ChartCmp.GaugeDiff.ev_diff {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h h' lam : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (h' - ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h - lam) =
      ev ![a, b] h' - ev ![comp1 φ a, comp1 φ b] h - ev ![a, b] lam := by sorry
