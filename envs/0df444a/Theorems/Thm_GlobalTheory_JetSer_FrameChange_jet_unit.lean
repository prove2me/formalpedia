-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_FrameChange_jet_unit
-- name    : GlobalTheory.JetSer.FrameChange.jet_unit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:15.773466+00:00
-- url     : https://prove2.me/theorems/fe1fb7f9-4a7e-44c6-a526-7683401ab86f
-- title:
--   Frame Change: jet unit
-- statement:
--   The Frame Change construction uses the jet unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean#L216-L219

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

theorem GlobalTheory.JetSer.FrameChange.jet_unit {R : Type} [CommRing R] {κ : Type} [Finite κ] {X : Scheme.{0}}
    {p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X} {U : X.Opens} {f : Γ(X, U)ˣ} {g : MvPowerSeries κ R}
    (h : HasSer p U f.val g) (m : ℕ) : toJet m g = (uv (p m) U f).val := by sorry
