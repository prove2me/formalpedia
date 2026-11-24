-- Prove2me | Theorems.Thm_GlobalTheory_FrameBaseChange_point_bc
-- name    : GlobalTheory.FrameBaseChange.point_bc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:37:20.336456+00:00
-- url     : https://prove2.me/theorems/52dc9583-7762-4ccc-a766-f26b9907ab09
-- title:
--   Frame Base Change: point bc
-- statement:
--   The Frame Base Change construction uses the point bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsFrameRawChartBaseChange.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsFrameRawChartBaseChange.lean#L102-L105

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsFrameRawChartBaseChange
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameBaseChange
open MvPolynomial (X C)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
variable {ψ x0} {d : ℕ} {x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G} {x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G}

theorem GlobalTheory.FrameBaseChange.point_bc (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    rjpt (spMap ψ ≫ x0) d x' m i = rjBC ψ x0 d m n ≫ rjpt x0 d x m i := by sorry
