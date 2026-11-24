-- Prove2me | Theorems.Thm_GlobalTheory_ChartAction_actSt_of
-- name    : GlobalTheory.ChartAction.actSt_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:58.398795+00:00
-- url     : https://prove2.me/theorems/561fbcbc-d115-4027-8bb3-7221c92dcd31
-- title:
--   Chart Action: act St of
-- statement:
--   The Chart Action construction uses the act St of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ActStOf.lean#L19-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ActStOf.lean#L19-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ActStOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartAction

theorem GlobalTheory.ChartAction.actSt_of (_ : JetAlgSt) (hR : RepSt) (hM : MapSt) : ActSt := by sorry
