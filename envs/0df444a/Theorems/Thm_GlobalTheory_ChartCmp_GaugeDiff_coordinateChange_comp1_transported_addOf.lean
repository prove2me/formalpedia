-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_coordinateChange_comp1_transported_addOf
-- name    : GlobalTheory.ChartCmp.GaugeDiff.coordinateChange_comp1_transported_addOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:35:38.174036+00:00
-- url     : https://prove2.me/theorems/33160c3c-dd41-5f14-a1da-e9638e678bed
-- title:
--   Gauge Diff: coordinate Change comp1 transported add Of
-- statement:
--   The Gauge Diff construction uses the coordinate Change comp1 transported add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L79-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L79-L102

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

theorem GlobalTheory.ChartCmp.GaugeDiff.coordinateChange_comp1_transported_addOf {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (F F' : Fin d → PS k 2 d) (hBF : GP F)
    (hF : ∀ i, F' i = transF F φ φi i) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 φ (addOf F' a b) = addOf F (comp1 φ a) (comp1 φ b) := by sorry
