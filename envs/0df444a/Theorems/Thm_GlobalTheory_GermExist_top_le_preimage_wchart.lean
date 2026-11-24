-- Prove2me | Theorems.Thm_GlobalTheory_GermExist_top_le_preimage_wchart
-- name    : GlobalTheory.GermExist.top_le_preimage_wchart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:19.13535+00:00
-- url     : https://prove2.me/theorems/f48f4bbd-07f3-4bb8-aadf-5d40df3e5b59
-- title:
--   Germ Exist: top le preimage wchart
-- statement:
--   The Germ Exist construction uses the top le preimage wchart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TopLePreimageWchart.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TopLePreimageWchart.lean#L32-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TopLePreimageWchart
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GermExist

theorem GlobalTheory.GermExist.top_le_preimage_wchart {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : L.ι) (e : Z ⟶ Y) (h : ∀ k, ⊤ ≤ (e ≫ φ k) ⁻¹ᵁ L.U j) : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ (fun _ => j) := by sorry
