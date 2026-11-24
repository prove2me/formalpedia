-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_repSt_of_jetAlgSt
-- name    : GlobalTheory.JetSer.repSt_of_jetAlgSt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:12:16.062798+00:00
-- url     : https://prove2.me/theorems/dee1180d-c1f2-454e-8715-36977d36fa5c
-- title:
--   Jet Ser: rep St of jet Alg St
-- statement:
--   The Jet Ser construction uses the rep St of jet Alg St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RepJetAugCompTrunc.lean#L26-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RepJetAugCompTrunc.lean#L26-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
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
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]

theorem GlobalTheory.JetSer.repSt_of_jetAlgSt (hJ : JetAlgSt) : RepSt := by sorry
