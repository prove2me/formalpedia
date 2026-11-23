-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_FrameChange_evH_res
-- name    : GlobalTheory.JetSer.FrameChange.evH_res
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:34.405125+00:00
-- url     : https://prove2.me/theorems/08250bea-a599-4a82-a09b-6484bee74526
-- title:
--   Frame Change: ev H res
-- statement:
--   The Frame Change construction uses the ev H res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L25-L32

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

theorem GlobalTheory.JetSer.FrameChange.evH_res (p : Spec (CommRingCat.of A) ⟶ X) {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ p ⁻¹ᵁ V)
    (f : Γ(X, V)) : evH p U h ((X.presheaf.map (homOfLE hUV).op).hom f) = evH p V h' f := by sorry
