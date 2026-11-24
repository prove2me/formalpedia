-- Prove2me | Theorems.Thm_GlobalTheory_GermExist_germ_exists_unique
-- name    : GlobalTheory.GermExist.germ_exists_unique
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:55:27.71638+00:00
-- url     : https://prove2.me/theorems/a515cf20-c0f9-4a6d-a9a6-158510958f6f
-- title:
--   Germ Exist: germ exists unique
-- statement:
--   The Germ Exist construction uses the germ exists unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TopLePreimageWchart.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TopLePreimageWchart.lean#L54-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TopLePreimageWchart
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GermExist

theorem GlobalTheory.GermExist.germ_exists_unique : JetAlgSt → RepSt → SerSt → SerExSt → GermExSt := by sorry
