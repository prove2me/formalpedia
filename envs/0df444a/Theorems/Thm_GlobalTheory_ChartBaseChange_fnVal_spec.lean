-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_fnVal_spec
-- name    : GlobalTheory.ChartBaseChange.fnVal_spec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:29.458122+00:00
-- url     : https://prove2.me/theorems/7d347192-8ee9-404b-a1a1-cc83dc71c8e1
-- title:
--   Chart Base Change: fn Val spec
-- statement:
--   The Chart Base Change construction uses the fn Val spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L29-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {A B : Type} [CommRing A] [CommRing B] {X Y : Scheme.{0}}

theorem GlobalTheory.ChartBaseChange.fnVal_spec (θ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom θ) ≫ p) ⁻¹ᵁ U ∧
      fnVal (Spec.map (CommRingCat.ofHom θ) ≫ p) U f = θ (fnVal p U f) := by sorry
