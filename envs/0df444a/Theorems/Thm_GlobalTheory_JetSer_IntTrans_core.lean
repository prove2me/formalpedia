-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_IntTrans_core
-- name    : GlobalTheory.JetSer.IntTrans.core
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:12.107965+00:00
-- url     : https://prove2.me/theorems/681cbc70-fc1d-420c-85c4-1f8d800f9415
-- title:
--   Int Trans: core
-- statement:
--   The Int Trans construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L141-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L141-L192

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
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem GlobalTheory.JetSer.IntTrans.core (hN : NabTransSt) {O : Type} [CommRing O] [StarRing O] {B B' : FB k d O} {φ φi : Pt k 1 d}
    {ε : PS k 2 d} (r : Related B B' φ φi ε) (h : PS k 2 d) (hh : B.IsCanonGauge k h) :
    ∃ h' : PS k 2 d, B'.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] ε ^ m =
        ev (n := 1) ![φ] f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B'.nabVal k h' w0 m f' u P = B.nabVal k h w0 m f (fun l => (dLin φ).mulVec (u l)) P := by sorry
