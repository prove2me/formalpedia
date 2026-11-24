-- Prove2me | Theorems.Thm_GlobalTheory_JetMap_mapSt_and_dLinSt
-- name    : GlobalTheory.JetMap.mapSt_and_dLinSt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:23.989314+00:00
-- url     : https://prove2.me/theorems/359d12b6-baa2-46ee-8fc6-29b25429c8a7
-- title:
--   Jet Map: map St and d Lin St
-- statement:
--   The Jet Map construction uses the map St and d Lin St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ToJetOneEqSum.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ToJetOneEqSum.lean#L100-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ToJetOneEqSum
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
open GlobalTheory GlobalTheory.JetMap

theorem GlobalTheory.JetMap.mapSt_and_dLinSt : JetAlgSt → RepSt → MapSt ∧ DLinSt := by sorry
