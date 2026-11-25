-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_coordinateChange_comp1_intertwines_action
-- name    : GlobalTheory.ChartCmp.GaugeDiff.coordinateChange_comp1_intertwines_action
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:35:34.180851+00:00
-- url     : https://prove2.me/theorems/98e36d4d-fbc1-50bc-add8-707accf475b7
-- title:
--   Gauge Diff: coordinate Change comp1 intertwines action
-- statement:
--   The Gauge Diff construction uses the coordinate Change comp1 intertwines action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean#L104-L109

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

theorem GlobalTheory.ChartCmp.GaugeDiff.coordinateChange_comp1_intertwines_action {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (A A' : Pt k 1 d) (hAa : GP A)
    (hA : A' = comp1 φi (comp1 A φ)) (x : Pt k n d) (hx : GP x) :
    comp1 φ (comp1 A' x) = comp1 A (comp1 φ x) := by sorry
