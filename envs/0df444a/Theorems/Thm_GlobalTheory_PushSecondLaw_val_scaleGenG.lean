-- Prove2me | Theorems.Thm_GlobalTheory_PushSecondLaw_val_scaleGenG
-- name    : GlobalTheory.PushSecondLaw.val_scaleGenG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:09.595712+00:00
-- url     : https://prove2.me/theorems/68db3bdd-d304-4778-a201-9210bd159615
-- title:
--   Push Second Law: val scale Gen G
-- statement:
--   The Push Second Law construction uses the val scale Gen G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondPartialLawPushAlongTripleMap.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondPartialLawPushAlongTripleMap.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondPartialLawPushAlongTripleMap
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
open GlobalTheory GlobalTheory.PushSecondLaw
open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.PushSecondLaw.val_scaleGenG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
    (c : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J := by sorry
