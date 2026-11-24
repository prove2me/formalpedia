-- Prove2me | Theorems.Thm_GlobalTheory_JetMap_toJet_one_eq_sum
-- name    : GlobalTheory.JetMap.toJet_one_eq_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:39:28.369713+00:00
-- url     : https://prove2.me/theorems/46e2e7c7-c8b1-4fa4-8c2c-ec08d3643ed5
-- title:
--   Jet Map: to Jet one eq sum
-- statement:
--   The Jet Map construction uses the to Jet one eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ToJetOneEqSum.lean#L47-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ToJetOneEqSum.lean#L47-L73

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

theorem GlobalTheory.JetMap.toJet_one_eq_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (g : MvPowerSeries κ R)
    (hg : constantCoeff g = 0) :
    toJet 1 g = ∑ p, coeff (Finsupp.single p 1) g • zR (R := R) 1 p := by sorry
