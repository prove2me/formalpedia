-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_FrameChange_evH_pull
-- name    : GlobalTheory.JetSer.FrameChange.evH_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:41:00.346267+00:00
-- url     : https://prove2.me/theorems/3992dc7c-0039-4408-814c-1ac2e2ccd170
-- title:
--   Frame Change: ev H pull
-- statement:
--   The Frame Change construction uses the ev H pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L34-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {A : Type} [CommRing A] {X Y : Scheme.{0}}

theorem GlobalTheory.JetSer.FrameChange.evH_pull (p : Spec (CommRingCat.of A) ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ (q ⁻¹ᵁ V))
    (h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V) (f : Γ(X, V)) : evH p _ h ((q.app V).hom f) = evH (p ≫ q) V h' f := by sorry
