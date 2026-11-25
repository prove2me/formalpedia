-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_pullLE
-- name    : GlobalTheory.AbLaw.SecOn.chart_pullLE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:29.703977+00:00
-- url     : https://prove2.me/theorems/03c6d80f-24f5-568f-8493-3e13afcad5ce
-- title:
--   Sec On: chart pull LE
-- statement:
--   The Sec On construction uses the chart pull LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L191-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}

theorem GlobalTheory.AbLaw.SecOn.chart_pullLE (hM : M.IsLB) (π : X' ⟶ X) {V' : X'.Opens} (e : V' ≤ π ⁻¹ᵁ V)
    (j : (M.pull π).ι) (h : V ≤ M.U (j PUnit.unit)) (h' : V' ≤ (M.pull π).U j) (s : SecOn M V) :
    chart (LB.isLB_pull hM π) j h' (pullLE M π V V' e s) =
      (π.appLE V V' e).hom (chart hM (j PUnit.unit) h s) := by sorry
