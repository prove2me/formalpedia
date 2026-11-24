-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_FrameChange_gen_change
-- name    : GlobalTheory.JetSer.FrameChange.gen_change
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:24.528669+00:00
-- url     : https://prove2.me/theorems/330af65b-9b9f-4058-b4b6-97c018a918b1
-- title:
--   Frame Change: gen change
-- statement:
--   The Frame Change construction uses the gen change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L78-L85

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

theorem GlobalTheory.JetSer.FrameChange.gen_change (L : LB X) (j j' : L.ι) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j)) (h' : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j')) :
    uv p _ (t.s (fun _ => j)) = (∏ k, hv L j j' (p ≫ φ k) ^ ε k) * uv p _ (t.s (fun _ => j')) := by sorry
