-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_biadd_gauge_diff
-- name    : GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:37:36.280835+00:00
-- url     : https://prove2.me/theorems/2be5ea0e-a534-4e05-9d96-2bd05ba546c0
-- title:
--   Gauge Diff: biadd gauge diff
-- statement:
--   The Gauge Diff construction uses the biadd gauge diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L146-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L146-L334

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

theorem GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ)
    (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) (J : JRel m B B' φ φi ε)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d)
    (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h') (hlam0 : MvPowerSeries.constantCoeff lam = 0)
    (hε : FB.expS k lam = FB.toK k ε) :
    Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0),
      comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by sorry
