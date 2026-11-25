-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_PushAd_carried_trans
-- name    : GlobalTheory.ChartCmp.PushAd.carried_trans
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:05:18.709913+00:00
-- url     : https://prove2.me/theorems/fbe84c16-a2fc-5ae2-bea8-f047b0fe603c
-- title:
--   Push Ad: carried trans
-- statement:
--   The Push Ad construction uses the carried trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AdjointnessSeriesTransportFrames.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AdjointnessSeriesTransportFrames.lean#L36-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.PushAd
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}

theorem GlobalTheory.ChartCmp.PushAd.carried_trans (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y)
    (z : Z) (p p' : K → L.ι) (q q' : K → L'.ι) (hp : r z ∈ LB.wchart L (fun k => φ k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ k ≫ F) p') (hq : r z ∈ LB.wchart L' φ q) (hq' : r z ∈ LB.wchart L' φ q') :
    (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) =
      trF (fun k => φ k ≫ F) ε r z p p' *
        ((∏ k, gw w (r ≫ φ k) z (p' k) (q' k) ^ ε k) * gm r z (LB.wchart L' φ q') (g.s q')) := by sorry
