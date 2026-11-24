-- Prove2me | Theorems.Thm_GlobalTheory_JetMap_isFPt_comp
-- name    : GlobalTheory.JetMap.isFPt_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:50.569886+00:00
-- url     : https://prove2.me/theorems/65b21663-86b9-42f5-a2d4-d4d396acea9a
-- title:
--   Jet Map: is FPt comp
-- statement:
--   The Jet Map construction uses the is FPt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ToJetOneEqSum.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ToJetOneEqSum.lean#L12-L19

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

theorem GlobalTheory.JetMap.isFPt_comp {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']
    {κ : Type} {y : Fam G κ} (hy : IsFPt y) (f : G ⟶ G') (hf : η[G] ≫ f = η[G']) :
    IsFPt (fun m => y m ≫ f : Fam G' κ) := by sorry
