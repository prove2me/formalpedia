-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_IntTrans_actK_eq
-- name    : GlobalTheory.JetSer.IntTrans.actK_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:42.370369+00:00
-- url     : https://prove2.me/theorems/60e2388a-e568-44e8-9da0-33153d83708c
-- title:
--   Int Trans: act K eq
-- statement:
--   The Int Trans construction uses the act K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L205-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L205-L207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] {d : ℕ}
  {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {C : FB k d O}

theorem GlobalTheory.JetSer.IntTrans.actK_eq (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a)) (a : O) : C.actK k a = B.actK k a := by sorry
