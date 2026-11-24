-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_fnVal_comp
-- name    : GlobalTheory.ChartBaseChange.fnVal_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:08.535908+00:00
-- url     : https://prove2.me/theorems/2078458a-9684-43e6-b7b5-1763d90a0075
-- title:
--   Chart Base Change: fn Val comp
-- statement:
--   The Chart Base Change construction uses the fn Val comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L19-L27

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

theorem GlobalTheory.ChartBaseChange.fnVal_comp (r : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (V : Y.Opens) (f : Γ(Y, V)) :
    fnVal r (q ⁻¹ᵁ V) ((q.app V).hom f) = fnVal (r ≫ q) V f := by sorry
