-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_IntTrans_nabVal_eq
-- name    : GlobalTheory.JetSer.IntTrans.nabVal_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:36.471276+00:00
-- url     : https://prove2.me/theorems/200d81ad-0e4b-43cc-8548-e4058210c650
-- title:
--   Int Trans: nab Val eq
-- statement:
--   The Int Trans construction uses the nab Val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L232-L236

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

theorem GlobalTheory.JetSer.IntTrans.nabVal_eq (hF : C.G.F = mP (algebraMap R k) B.G.F) (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a))
    (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial ι k) : C.nabVal k h w0 m f u P = B.nabVal k h w0 m f u P := by sorry
