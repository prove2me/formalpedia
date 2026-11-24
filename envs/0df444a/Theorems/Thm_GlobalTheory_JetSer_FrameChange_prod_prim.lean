-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_FrameChange_prod_prim
-- name    : GlobalTheory.JetSer.FrameChange.prod_prim
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:28.845582+00:00
-- url     : https://prove2.me/theorems/63c88f8d-b9b9-4f8d-b30d-cb1f7f2f947d
-- title:
--   Frame Change: prod prim
-- statement:
--   The Frame Change construction uses the prod prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L130-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L130-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
variable {G}

theorem GlobalTheory.JetSer.FrameChange.prod_prim {T : Over S} (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h (x.left ≫ primφ w k) ^ primε k = h x.left * (lamV h x (x ≫ w))⁻¹ := by sorry
