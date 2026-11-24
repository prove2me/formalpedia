-- Prove2me | Theorems.Thm_GlobalTheory_FrameBaseChange_val_scale
-- name    : GlobalTheory.FrameBaseChange.val_scale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:09.815799+00:00
-- url     : https://prove2.me/theorems/a71647c6-2620-4c46-93e4-5602e5aad789
-- title:
--   Frame Base Change: val scale
-- statement:
--   The Frame Base Change construction uses the val scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsFrameRawChartBaseChange.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsFrameRawChartBaseChange.lean#L42-L47

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

theorem GlobalTheory.FrameBaseChange.val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι} (hJ : Good Xo.univ.t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (Formalism.L2.Pj.scaleGen φ ε c t) r z J = gm r z ⊤ c * val t r z J := by sorry
