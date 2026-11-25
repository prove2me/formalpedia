-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_PushAd_exists_carried
-- name    : GlobalTheory.ChartCmp.PushAd.exists_carried
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:44:38.615597+00:00
-- url     : https://prove2.me/theorems/3af3e1e0-9064-5ba8-bec4-7386bc926436
-- title:
--   Push Ad: exists carried
-- statement:
--   The Push Ad construction uses the exists carried property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AdjointnessSeriesTransportFrames.lean#L49-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AdjointnessSeriesTransportFrames.lean#L49-L84

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

theorem GlobalTheory.ChartCmp.PushAd.exists_carried (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) :
    ∃ g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), g'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val g' r z J = (∏ k, wv w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by sorry
