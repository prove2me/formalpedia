-- Prove2me | Theorems.Thm_GlobalTheory_ChartAction_rep_unique
-- name    : GlobalTheory.ChartAction.rep_unique
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:26.567205+00:00
-- url     : https://prove2.me/theorems/cdea1f37-043c-4e6d-bcc7-07b1d2dd80db
-- title:
--   Chart Action: rep unique
-- statement:
--   The Chart Action construction uses the rep unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ActStOf.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ActStOf.lean#L12-L17

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

theorem GlobalTheory.ChartAction.rep_unique (hR : RepSt) {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ}
    {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {κ : Type} [Finite κ] {a b : Fin d → MvPowerSeries κ R}
    {y z : Fam G κ} (ha : Rep x a y) (hb : Rep x b z) (h : y = z) : a = b := by sorry
