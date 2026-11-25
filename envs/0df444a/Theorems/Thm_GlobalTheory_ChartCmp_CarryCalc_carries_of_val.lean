-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_carries_of_val
-- name    : GlobalTheory.ChartCmp.CarryCalc.carries_of_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:04:12.567163+00:00
-- url     : https://prove2.me/theorems/a9cfbf98-e85d-54a6-a843-165b16ed5072
-- title:
--   Carry Calc: carries of val
-- statement:
--   The Carry Calc construction uses the carries of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CarriesLinCombGeneratorCalculus.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CarriesLinCombGeneratorCalculus.lean#L44-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CarryCalc
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem GlobalTheory.ChartCmp.CarryCalc.carries_of_val {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {φ : K → (Y ⟶ X')}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (hg : g.IsGen)
    (hg' : g'.IsGen) (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val g' (𝟙 Y) y J = (∏ k, fac w y J J' (𝟙 Y ≫ φ k) ^ ε k) * val g (𝟙 Y) y J') : Carries L F w φ ε g g' := by sorry
